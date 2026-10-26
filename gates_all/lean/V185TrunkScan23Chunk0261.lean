import V185TrunkScan23Chunk0260

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1544301 : List Nat := [1, 5, 1, 1, 2, 1, 1, 4, 2, 2, 3]
def baseStart_1544301 : Nat := 118140960795 + 1544301 * 2 ^ 59
def prefixEnd_1544301 : Nat := 4983230072969 + 3 ^ 40 * 1544301 * 2
def baseEnd_1544301 : Nat := 792968688219067648935395

theorem tailTrace_1544301 : CollatzResearch.WordTrace tailWord_1544301 prefixEnd_1544301 792968688219067648935395 := by
  unfold tailWord_1544301
  simp only [CollatzResearch.WordTrace]
  refine ⟨56325284778268697458048757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37550189852179131638699171 56325284778268697458048757)
  ·
    refine ⟨5280495447962690386692071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56325284778268697458048757 5280495447962690386692071)
    ·
      refine ⟨7920743171944035580038107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5280495447962690386692071 7920743171944035580038107)
      ·
        refine ⟨11881114757916053370057161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7920743171944035580038107 11881114757916053370057161)
        ·
          refine ⟨8910836068437040027542871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11881114757916053370057161 8910836068437040027542871)
          ·
            refine ⟨13366254102655560041314307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8910836068437040027542871 13366254102655560041314307)
            ·
              refine ⟨20049381153983340061971461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13366254102655560041314307 20049381153983340061971461)
              ·
                refine ⟨3759258966371876261619649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20049381153983340061971461 3759258966371876261619649)
                ·
                  refine ⟨2819444224778907196214737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3759258966371876261619649 2819444224778907196214737)
                  ·
                    refine ⟨2114583168584180397161053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2819444224778907196214737 2114583168584180397161053)
                    ·
                      refine ⟨792968688219067648935395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2114583168584180397161053 792968688219067648935395)
                      ·
                        rfl

theorem cell23_1544301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_1544301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1544301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1544301 prefixEnd_1544301 := by exact prefixLift 1544301
  have htrace : WordTrace (prefixWord ++ tailWord_1544301) baseStart_1544301 baseEnd_1544301 := by
    simpa [prefixWord, tailWord_1544301, baseEnd_1544301] using wordTrace_append hprefix tailTrace_1544301
  have hstable : (prefixWord ++ tailWord_1544301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544301).length < 2 ^ (prefixWord ++ tailWord_1544301).sum := by decide
  have hdescent : baseEnd_1544301 < baseStart_1544301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544304 : List Nat := [2, 1, 1, 1, 5, 2, 1, 4, 6]
def baseStart_1544304 : Nat := 118140960795 + 1544304 * 2 ^ 59
def prefixEnd_1544304 : Nat := 4983230072969 + 3 ^ 40 * 1544304 * 2
def baseEnd_1544304 : Nat := 88107803184559015244209

theorem tailTrace_1544304 : CollatzResearch.WordTrace tailWord_1544304 prefixEnd_1544304 88107803184559015244209 := by
  unfold tailWord_1544304
  simp only [CollatzResearch.WordTrace]
  refine ⟨28162697098628914485203983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37550262798171885980271977 28162697098628914485203983)
  ·
    refine ⟨42244045647943371727805975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28162697098628914485203983 42244045647943371727805975)
    ·
      refine ⟨63366068471915057591708963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42244045647943371727805975 63366068471915057591708963)
      ·
        refine ⟨95049102707872586387563445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63366068471915057591708963 95049102707872586387563445)
        ·
          refine ⟨8910853378863054973834073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 95049102707872586387563445 8910853378863054973834073)
          ·
            refine ⟨6683140034147291230375555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8910853378863054973834073 6683140034147291230375555)
            ·
              refine ⟨10024710051220936845563333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6683140034147291230375555 10024710051220936845563333)
              ·
                refine ⟨1879633134603925658543125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10024710051220936845563333 1879633134603925658543125)
                ·
                  refine ⟨88107803184559015244209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1879633134603925658543125 88107803184559015244209)
                  ·
                    rfl

theorem cell23_1544304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 4, 6].length) (baseStart_1544304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1544304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1544304 prefixEnd_1544304 := by exact prefixLift 1544304
  have htrace : WordTrace (prefixWord ++ tailWord_1544304) baseStart_1544304 baseEnd_1544304 := by
    simpa [prefixWord, tailWord_1544304, baseEnd_1544304] using wordTrace_append hprefix tailTrace_1544304
  have hstable : (prefixWord ++ tailWord_1544304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544304).length < 2 ^ (prefixWord ++ tailWord_1544304).sum := by decide
  have hdescent : baseEnd_1544304 < baseStart_1544304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544341 : List Nat := [1, 3, 2, 1, 1, 1, 5, 1, 1, 5, 2]
def baseStart_1544341 : Nat := 118140960795 + 1544341 * 2 ^ 59
def prefixEnd_1544341 : Nat := 4983230072969 + 3 ^ 40 * 1544341 * 2
def baseEnd_1544341 : Nat := 792989227445247492435211

theorem tailTrace_1544341 : CollatzResearch.WordTrace tailWord_1544341 prefixEnd_1544341 792989227445247492435211 := by
  unfold tailWord_1544341
  simp only [CollatzResearch.WordTrace]
  refine ⟨56326743698123784289504877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37551162465415856193003251 56326743698123784289504877)
  ·
    refine ⟨21122528886796419108564329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56326743698123784289504877 21122528886796419108564329)
    ·
      refine ⟨15841896665097314331423247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21122528886796419108564329 15841896665097314331423247)
      ·
        refine ⟨23762844997645971497134871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15841896665097314331423247 23762844997645971497134871)
        ·
          refine ⟨35644267496468957245702307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23762844997645971497134871 35644267496468957245702307)
          ·
            refine ⟨53466401244703435868553461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35644267496468957245702307 53466401244703435868553461)
            ·
              refine ⟨5012475116690947112676887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53466401244703435868553461 5012475116690947112676887)
              ·
                refine ⟨7518712675036420669015331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5012475116690947112676887 7518712675036420669015331)
                ·
                  refine ⟨11278069012554631003522997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7518712675036420669015331 11278069012554631003522997)
                  ·
                    refine ⟨1057318969926996656580281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11278069012554631003522997 1057318969926996656580281)
                    ·
                      refine ⟨792989227445247492435211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1057318969926996656580281 792989227445247492435211)
                      ·
                        rfl

theorem cell23_1544341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 5, 2].length) (baseStart_1544341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1544341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1544341 prefixEnd_1544341 := by exact prefixLift 1544341
  have htrace : WordTrace (prefixWord ++ tailWord_1544341) baseStart_1544341 baseEnd_1544341 := by
    simpa [prefixWord, tailWord_1544341, baseEnd_1544341] using wordTrace_append hprefix tailTrace_1544341
  have hstable : (prefixWord ++ tailWord_1544341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544341).length < 2 ^ (prefixWord ++ tailWord_1544341).sum := by decide
  have hdescent : baseEnd_1544341 < baseStart_1544341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544365 : List Nat := [1, 5, 2, 1, 2, 2, 2, 1, 3, 1, 3]
def baseStart_1544365 : Nat := 118140960795 + 1544365 * 2 ^ 59
def prefixEnd_1544365 : Nat := 4983230072969 + 3 ^ 40 * 1544365 * 2
def baseEnd_1544365 : Nat := 793001550980955398535101

theorem tailTrace_1544365 : CollatzResearch.WordTrace tailWord_1544365 prefixEnd_1544365 793001550980955398535101 := by
  unfold tailWord_1544365
  simp only [CollatzResearch.WordTrace]
  refine ⟨56327619050036836388378549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37551746033357890925585699 56327619050036836388378549)
  ·
    refine ⟨5280714285940953411410489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56327619050036836388378549 5280714285940953411410489)
    ·
      refine ⟨3960535714455715058557867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5280714285940953411410489 3960535714455715058557867)
      ·
        refine ⟨5940803571683572587836801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3960535714455715058557867 5940803571683572587836801)
        ·
          refine ⟨4455602678762679440877601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5940803571683572587836801 4455602678762679440877601)
          ·
            refine ⟨3341702009072009580658201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4455602678762679440877601 3341702009072009580658201)
            ·
              refine ⟨2506276506804007185493651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3341702009072009580658201 2506276506804007185493651)
              ·
                refine ⟨3759414760206010778240477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2506276506804007185493651 3759414760206010778240477)
                ·
                  refine ⟨1409780535077254041840179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3759414760206010778240477 1409780535077254041840179)
                  ·
                    refine ⟨2114670802615881062760269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1409780535077254041840179 2114670802615881062760269)
                    ·
                      refine ⟨793001550980955398535101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2114670802615881062760269 793001550980955398535101)
                      ·
                        rfl

theorem cell23_1544365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_1544365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1544365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1544365 prefixEnd_1544365 := by exact prefixLift 1544365
  have htrace : WordTrace (prefixWord ++ tailWord_1544365) baseStart_1544365 baseEnd_1544365 := by
    simpa [prefixWord, tailWord_1544365, baseEnd_1544365] using wordTrace_append hprefix tailTrace_1544365
  have hstable : (prefixWord ++ tailWord_1544365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544365).length < 2 ^ (prefixWord ++ tailWord_1544365).sum := by decide
  have hdescent : baseEnd_1544365 < baseStart_1544365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544385 : List Nat := [1, 2, 6, 1, 2, 1, 2, 2, 1, 5]
def baseStart_1544385 : Nat := 118140960795 + 1544385 * 2 ^ 59
def prefixEnd_1544385 : Nat := 4983230072969 + 3 ^ 40 * 1544385 * 2
def baseEnd_1544385 : Nat := 264337273531348440095003

theorem tailTrace_1544385 : CollatzResearch.WordTrace tailWord_1544385 prefixEnd_1544385 264337273531348440095003 := by
  unfold tailWord_1544385
  simp only [CollatzResearch.WordTrace]
  refine ⟨56328348509964379804106609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37552232339976253202737739 56328348509964379804106609)
  ·
    refine ⟨42246261382473284853079957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56328348509964379804106609 42246261382473284853079957)
    ·
      refine ⟨1980293502303435227488123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 42246261382473284853079957 1980293502303435227488123)
      ·
        refine ⟨2970440253455152841232185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1980293502303435227488123 2970440253455152841232185)
        ·
          refine ⟨2227830190091364630924139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2970440253455152841232185 2227830190091364630924139)
          ·
            refine ⟨3341745285137046946386209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2227830190091364630924139 3341745285137046946386209)
            ·
              refine ⟨2506308963852785209789657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3341745285137046946386209 2506308963852785209789657)
              ·
                refine ⟨1879731722889588907342243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2506308963852785209789657 1879731722889588907342243)
                ·
                  refine ⟨2819597584334383361013365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1879731722889588907342243 2819597584334383361013365)
                  ·
                    refine ⟨264337273531348440095003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2819597584334383361013365 264337273531348440095003)
                    ·
                      rfl

theorem cell23_1544385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_1544385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1544385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1544385 prefixEnd_1544385 := by exact prefixLift 1544385
  have htrace : WordTrace (prefixWord ++ tailWord_1544385) baseStart_1544385 baseEnd_1544385 := by
    simpa [prefixWord, tailWord_1544385, baseEnd_1544385] using wordTrace_append hprefix tailTrace_1544385
  have hstable : (prefixWord ++ tailWord_1544385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544385).length < 2 ^ (prefixWord ++ tailWord_1544385).sum := by decide
  have hdescent : baseEnd_1544385 < baseStart_1544385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544388 : List Nat := [2, 3, 3, 1, 2, 1, 1, 4, 1, 1, 4]
def baseStart_1544388 : Nat := 118140960795 + 1544388 * 2 ^ 59
def prefixEnd_1544388 : Nat := 4983230072969 + 3 ^ 40 * 1544388 * 2
def baseEnd_1544388 : Nat := 793013361036008808547495

theorem tailTrace_1544388 : CollatzResearch.WordTrace tailWord_1544388 prefixEnd_1544388 793013361036008808547495 := by
  unfold tailWord_1544388
  simp only [CollatzResearch.WordTrace]
  refine ⟨28164228964476755658232909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37552305285969007544310545 28164228964476755658232909)
  ·
    refine ⟨10561585861678783371837341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28164228964476755658232909 10561585861678783371837341)
    ·
      refine ⟨3960594698129543764439003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10561585861678783371837341 3960594698129543764439003)
      ·
        refine ⟨5940892047194315646658505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3960594698129543764439003 5940892047194315646658505)
        ·
          refine ⟨4455669035395736734993879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5940892047194315646658505 4455669035395736734993879)
          ·
            refine ⟨6683503553093605102490819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4455669035395736734993879 6683503553093605102490819)
            ·
              refine ⟨10025255329640407653736229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6683503553093605102490819 10025255329640407653736229)
              ·
                refine ⟨1879735374307576435075543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10025255329640407653736229 1879735374307576435075543)
                ·
                  refine ⟨2819603061461364652613315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1879735374307576435075543 2819603061461364652613315)
                  ·
                    refine ⟨4229404592192046978919973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2819603061461364652613315 4229404592192046978919973)
                    ·
                      refine ⟨793013361036008808547495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4229404592192046978919973 793013361036008808547495)
                      ·
                        rfl

theorem cell23_1544388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_1544388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1544388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1544388 prefixEnd_1544388 := by exact prefixLift 1544388
  have htrace : WordTrace (prefixWord ++ tailWord_1544388) baseStart_1544388 baseEnd_1544388 := by
    simpa [prefixWord, tailWord_1544388, baseEnd_1544388] using wordTrace_append hprefix tailTrace_1544388
  have hstable : (prefixWord ++ tailWord_1544388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544388).length < 2 ^ (prefixWord ++ tailWord_1544388).sum := by decide
  have hdescent : baseEnd_1544388 < baseStart_1544388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544394 : List Nat := [3, 1, 2, 1, 3, 1, 3, 9]
def baseStart_1544394 : Nat := 118140960795 + 1544394 * 2 ^ 59
def prefixEnd_1544394 : Nat := 4983230072969 + 3 ^ 40 * 1544394 * 2
def baseEnd_1544394 : Nat := 29370979330367992039721

theorem tailTrace_1544394 : CollatzResearch.WordTrace tailWord_1544394 prefixEnd_1544394 29370979330367992039721 := by
  unfold tailWord_1544394
  simp only [CollatzResearch.WordTrace]
  refine ⟨14082169191732943585296059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37552451177954516227456157 14082169191732943585296059)
  ·
    refine ⟨21123253787599415377944089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14082169191732943585296059 21123253787599415377944089)
    ·
      refine ⟨15842440340699561533458067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21123253787599415377944089 15842440340699561533458067)
      ·
        refine ⟨23763660511049342300187101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15842440340699561533458067 23763660511049342300187101)
        ·
          refine ⟨8911372691643503362570163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23763660511049342300187101 8911372691643503362570163)
          ·
            refine ⟨13367059037465255043855245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8911372691643503362570163 13367059037465255043855245)
            ·
              refine ⟨5012647139049470641445717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13367059037465255043855245 5012647139049470641445717)
              ·
                refine ⟨29370979330367992039721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5012647139049470641445717 29370979330367992039721)
                ·
                  rfl

theorem cell23_1544394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 9].length) (baseStart_1544394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1544394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1544394 prefixEnd_1544394 := by exact prefixLift 1544394
  have htrace : WordTrace (prefixWord ++ tailWord_1544394) baseStart_1544394 baseEnd_1544394 := by
    simpa [prefixWord, tailWord_1544394, baseEnd_1544394] using wordTrace_append hprefix tailTrace_1544394
  have hstable : (prefixWord ++ tailWord_1544394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544394).length < 2 ^ (prefixWord ++ tailWord_1544394).sum := by decide
  have hdescent : baseEnd_1544394 < baseStart_1544394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544408 : List Nat := [2, 1, 2, 2, 4, 1, 2, 3, 1, 2, 3]
def baseStart_1544408 : Nat := 118140960795 + 1544408 * 2 ^ 59
def prefixEnd_1544408 : Nat := 4983230072969 + 3 ^ 40 * 1544408 * 2
def baseEnd_1544408 : Nat := 793023630649098730297403

theorem tailTrace_1544408 : CollatzResearch.WordTrace tailWord_1544408 prefixEnd_1544408 793023630649098730297403 := by
  unfold tailWord_1544408
  simp only [CollatzResearch.WordTrace]
  refine ⟨28164593694440527366096939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37552791592587369821462585 28164593694440527366096939)
  ·
    refine ⟨42246890541660791049145409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28164593694440527366096939 42246890541660791049145409)
    ·
      refine ⟨31685167906245593286859057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42246890541660791049145409 31685167906245593286859057)
      ·
        refine ⟨23763875929684194965144293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31685167906245593286859057 23763875929684194965144293)
        ·
          refine ⟨4455726736815786555964555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23763875929684194965144293 4455726736815786555964555)
          ·
            refine ⟨6683590105223679833946833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4455726736815786555964555 6683590105223679833946833)
            ·
              refine ⟨5012692578917759875460125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6683590105223679833946833 5012692578917759875460125)
              ·
                refine ⟨1879759717094159953297547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5012692578917759875460125 1879759717094159953297547)
                ·
                  refine ⟨2819639575641239929946321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1879759717094159953297547 2819639575641239929946321)
                  ·
                    refine ⟨2114729681730929947459741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2819639575641239929946321 2114729681730929947459741)
                    ·
                      refine ⟨793023630649098730297403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2114729681730929947459741 793023630649098730297403)
                      ·
                        rfl

theorem cell23_1544408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 3, 1, 2, 3].length) (baseStart_1544408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1544408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1544408 prefixEnd_1544408 := by exact prefixLift 1544408
  have htrace : WordTrace (prefixWord ++ tailWord_1544408) baseStart_1544408 baseEnd_1544408 := by
    simpa [prefixWord, tailWord_1544408, baseEnd_1544408] using wordTrace_append hprefix tailTrace_1544408
  have hstable : (prefixWord ++ tailWord_1544408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544408).length < 2 ^ (prefixWord ++ tailWord_1544408).sum := by decide
  have hdescent : baseEnd_1544408 < baseStart_1544408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544455 : List Nat := [1, 1, 4, 5, 1, 1, 1, 2, 1, 3, 3]
def baseStart_1544455 : Nat := 118140960795 + 1544455 * 2 ^ 59
def prefixEnd_1544455 : Nat := 4983230072969 + 3 ^ 40 * 1544455 * 2
def baseEnd_1544455 : Nat := 793047764239860046409687

theorem tailTrace_1544455 : CollatzResearch.WordTrace tailWord_1544455 prefixEnd_1544455 793047764239860046409687 := by
  unfold tailWord_1544455
  simp only [CollatzResearch.WordTrace]
  refine ⟨56330901619710781759154819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37553934413140521172769879 56330901619710781759154819)
  ·
    refine ⟨84496352429566172638732229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56330901619710781759154819 84496352429566172638732229)
    ·
      refine ⟨15843066080543657369762293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84496352429566172638732229 15843066080543657369762293)
      ·
        refine ⟨1485287445050967878415215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15843066080543657369762293 1485287445050967878415215)
        ·
          refine ⟨2227931167576451817622823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1485287445050967878415215 2227931167576451817622823)
          ·
            refine ⟨3341896751364677726434235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2227931167576451817622823 3341896751364677726434235)
            ·
              refine ⟨5012845127047016589651353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3341896751364677726434235 5012845127047016589651353)
              ·
                refine ⟨3759633845285262442238515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5012845127047016589651353 3759633845285262442238515)
                ·
                  refine ⟨5639450767927893663357773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3759633845285262442238515 5639450767927893663357773)
                  ·
                    refine ⟨2114794037972960123759165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5639450767927893663357773 2114794037972960123759165)
                    ·
                      refine ⟨793047764239860046409687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2114794037972960123759165 793047764239860046409687)
                      ·
                        rfl

theorem cell23_1544455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_1544455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1544455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1544455 prefixEnd_1544455 := by exact prefixLift 1544455
  have htrace : WordTrace (prefixWord ++ tailWord_1544455) baseStart_1544455 baseEnd_1544455 := by
    simpa [prefixWord, tailWord_1544455, baseEnd_1544455] using wordTrace_append hprefix tailTrace_1544455
  have hstable : (prefixWord ++ tailWord_1544455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544455).length < 2 ^ (prefixWord ++ tailWord_1544455).sum := by decide
  have hdescent : baseEnd_1544455 < baseStart_1544455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544481 : List Nat := [1, 2, 3, 2, 1, 1, 3, 1, 2, 4, 3]
def baseStart_1544481 : Nat := 118140960795 + 1544481 * 2 ^ 59
def prefixEnd_1544481 : Nat := 4983230072969 + 3 ^ 40 * 1544481 * 2
def baseEnd_1544481 : Nat := 793061114736876944684567

theorem tailTrace_1544481 : CollatzResearch.WordTrace tailWord_1544481 prefixEnd_1544481 793061114736876944684567 := by
  unfold tailWord_1544481
  simp only [CollatzResearch.WordTrace]
  refine ⟨56331849917616588199601297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37554566611744392133067531 56331849917616588199601297)
  ·
    refine ⟨42248887438212441149700973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56331849917616588199601297 42248887438212441149700973)
    ·
      refine ⟨15843332789329665431137865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42248887438212441149700973 15843332789329665431137865)
      ·
        refine ⟨11882499591997249073353399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15843332789329665431137865 11882499591997249073353399)
        ·
          refine ⟨17823749387995873610030099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11882499591997249073353399 17823749387995873610030099)
          ·
            refine ⟨26735624081993810415045149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17823749387995873610030099 26735624081993810415045149)
            ·
              refine ⟨10025859030747678905641931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26735624081993810415045149 10025859030747678905641931)
              ·
                refine ⟨15038788546121518358462897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10025859030747678905641931 15038788546121518358462897)
                ·
                  refine ⟨11279091409591138768847173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15038788546121518358462897 11279091409591138768847173)
                  ·
                    refine ⟨2114829639298338519158845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11279091409591138768847173 2114829639298338519158845)
                    ·
                      refine ⟨793061114736876944684567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2114829639298338519158845 793061114736876944684567)
                      ·
                        rfl

theorem cell23_1544481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_1544481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1544481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1544481 prefixEnd_1544481 := by exact prefixLift 1544481
  have htrace : WordTrace (prefixWord ++ tailWord_1544481) baseStart_1544481 baseEnd_1544481 := by
    simpa [prefixWord, tailWord_1544481, baseEnd_1544481] using wordTrace_append hprefix tailTrace_1544481
  have hstable : (prefixWord ++ tailWord_1544481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544481).length < 2 ^ (prefixWord ++ tailWord_1544481).sum := by decide
  have hdescent : baseEnd_1544481 < baseStart_1544481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544488 : List Nat := [2, 1, 5, 1, 3, 1, 1, 1, 2, 6]
def baseStart_1544488 : Nat := 118140960795 + 1544488 * 2 ^ 59
def prefixEnd_1544488 : Nat := 4983230072969 + 3 ^ 40 * 1544488 * 2
def baseEnd_1544488 : Nat := 264354903033819472432345

theorem tailTrace_1544488 : CollatzResearch.WordTrace tailWord_1544488 prefixEnd_1544488 264354903033819472432345 := by
  unfold tailWord_1544488
  simp only [CollatzResearch.WordTrace]
  refine ⟨28166052614295614197553059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37554736819060818930070745 28166052614295614197553059)
  ·
    refine ⟨42249078921443421296329589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28166052614295614197553059 42249078921443421296329589)
    ·
      refine ⟨3960851148885320746530899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42249078921443421296329589 3960851148885320746530899)
      ·
        refine ⟨5941276723327981119796349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3960851148885320746530899 5941276723327981119796349)
        ·
          refine ⟨2227978771247992919923631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5941276723327981119796349 2227978771247992919923631)
          ·
            refine ⟨3341968156871989379885447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2227978771247992919923631 3341968156871989379885447)
            ·
              refine ⟨5012952235307984069828171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3341968156871989379885447 5012952235307984069828171)
              ·
                refine ⟨7519428352961976104742257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5012952235307984069828171 7519428352961976104742257)
                ·
                  refine ⟨5639571264721482078556693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7519428352961976104742257 5639571264721482078556693)
                  ·
                    refine ⟨264354903033819472432345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5639571264721482078556693 264354903033819472432345)
                    ·
                      rfl

theorem cell23_1544488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_1544488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1544488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1544488 prefixEnd_1544488 := by exact prefixLift 1544488
  have htrace : WordTrace (prefixWord ++ tailWord_1544488) baseStart_1544488 baseEnd_1544488 := by
    simpa [prefixWord, tailWord_1544488, baseEnd_1544488] using wordTrace_append hprefix tailTrace_1544488
  have hstable : (prefixWord ++ tailWord_1544488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544488).length < 2 ^ (prefixWord ++ tailWord_1544488).sum := by decide
  have hdescent : baseEnd_1544488 < baseStart_1544488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544495 : List Nat := [1, 1, 2, 1, 2, 1, 6, 3, 2, 2, 2]
def baseStart_1544495 : Nat := 118140960795 + 1544495 * 2 ^ 59
def prefixEnd_1544495 : Nat := 4983230072969 + 3 ^ 40 * 1544495 * 2
def baseEnd_1544495 : Nat := 793068303466039889909503

theorem tailTrace_1544495 : CollatzResearch.WordTrace tailWord_1544495 prefixEnd_1544495 793068303466039889909503 := by
  unfold tailWord_1544495
  simp only [CollatzResearch.WordTrace]
  refine ⟨56332360539565868590610939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37554907026377245727073959 56332360539565868590610939)
  ·
    refine ⟨84498540809348802885916409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56332360539565868590610939 84498540809348802885916409)
    ·
      refine ⟨63373905607011602164437307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84498540809348802885916409 63373905607011602164437307)
      ·
        refine ⟨95060858410517403246655961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63373905607011602164437307 95060858410517403246655961)
        ·
          refine ⟨71295643807888052434991971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95060858410517403246655961 71295643807888052434991971)
          ·
            refine ⟨106943465711832078652487957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71295643807888052434991971 106943465711832078652487957)
            ·
              refine ⟨5012974955242128686835373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 106943465711832078652487957 5012974955242128686835373)
              ·
                refine ⟨1879865608215798257563265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5012974955242128686835373 1879865608215798257563265)
                ·
                  refine ⟨1409899206161848693172449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1879865608215798257563265 1409899206161848693172449)
                  ·
                    refine ⟨1057424404621386519879337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1409899206161848693172449 1057424404621386519879337)
                    ·
                      refine ⟨793068303466039889909503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1057424404621386519879337 793068303466039889909503)
                      ·
                        rfl

theorem cell23_1544495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 3, 2, 2, 2].length) (baseStart_1544495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1544495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1544495 prefixEnd_1544495 := by exact prefixLift 1544495
  have htrace : WordTrace (prefixWord ++ tailWord_1544495) baseStart_1544495 baseEnd_1544495 := by
    simpa [prefixWord, tailWord_1544495, baseEnd_1544495] using wordTrace_append hprefix tailTrace_1544495
  have hstable : (prefixWord ++ tailWord_1544495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544495).length < 2 ^ (prefixWord ++ tailWord_1544495).sum := by decide
  have hdescent : baseEnd_1544495 < baseStart_1544495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544501 : List Nat := [1, 3, 3, 1, 2, 1, 3, 2, 7]
def baseStart_1544501 : Nat := 118140960795 + 1544501 * 2 ^ 59
def prefixEnd_1544501 : Nat := 4983230072969 + 3 ^ 40 * 1544501 * 2
def baseEnd_1544501 : Nat := 88119042705551874048275

theorem tailTrace_1544501 : CollatzResearch.WordTrace tailWord_1544501 prefixEnd_1544501 88119042705551874048275 := by
  unfold tailWord_1544501
  simp only [CollatzResearch.WordTrace]
  refine ⟨56332579377544131615329357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37555052918362754410219571 56332579377544131615329357)
  ·
    refine ⟨21124717266579049355748509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56332579377544131615329357 21124717266579049355748509)
    ·
      refine ⟨7921768974967143508405691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21124717266579049355748509 7921768974967143508405691)
      ·
        refine ⟨11882653462450715262608537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7921768974967143508405691 11882653462450715262608537)
        ·
          refine ⟨8911990096838036446956403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11882653462450715262608537 8911990096838036446956403)
          ·
            refine ⟨13367985145257054670434605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8911990096838036446956403 13367985145257054670434605)
            ·
              refine ⟨5012994429471395501412977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13367985145257054670434605 5012994429471395501412977)
              ·
                refine ⟨3759745822103546626059733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5012994429471395501412977 3759745822103546626059733)
                ·
                  refine ⟨88119042705551874048275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3759745822103546626059733 88119042705551874048275)
                  ·
                    rfl

theorem cell23_1544501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 2, 7].length) (baseStart_1544501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1544501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1544501 prefixEnd_1544501 := by exact prefixLift 1544501
  have htrace : WordTrace (prefixWord ++ tailWord_1544501) baseStart_1544501 baseEnd_1544501 := by
    simpa [prefixWord, tailWord_1544501, baseEnd_1544501] using wordTrace_append hprefix tailTrace_1544501
  have hstable : (prefixWord ++ tailWord_1544501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544501).length < 2 ^ (prefixWord ++ tailWord_1544501).sum := by decide
  have hdescent : baseEnd_1544501 < baseStart_1544501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544511 : List Nat := [1, 1, 2, 2, 4, 1, 1, 2, 1, 5, 3]
def baseStart_1544511 : Nat := 118140960795 + 1544511 * 2 ^ 59
def prefixEnd_1544511 : Nat := 4983230072969 + 3 ^ 40 * 1544511 * 2
def baseEnd_1544511 : Nat := 793076519156511827309429

theorem tailTrace_1544511 : CollatzResearch.WordTrace tailWord_1544511 prefixEnd_1544511 793076519156511827309429 := by
  unfold tailWord_1544511
  simp only [CollatzResearch.WordTrace]
  refine ⟨56332944107507903323193387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37555296071671935548795591 56332944107507903323193387)
  ·
    refine ⟨84499416161261854984790081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56332944107507903323193387 84499416161261854984790081)
    ·
      refine ⟨63374562120946391238592561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84499416161261854984790081 63374562120946391238592561)
      ·
        refine ⟨47530921590709793428944421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63374562120946391238592561 47530921590709793428944421)
        ·
          refine ⟨8912047798258086267927079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47530921590709793428944421 8912047798258086267927079)
          ·
            refine ⟨13368071697387129401890619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8912047798258086267927079 13368071697387129401890619)
            ·
              refine ⟨20052107546080694102835929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13368071697387129401890619 20052107546080694102835929)
              ·
                refine ⟨15039080659560520577126947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20052107546080694102835929 15039080659560520577126947)
                ·
                  refine ⟨22558620989340780865690421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15039080659560520577126947 22558620989340780865690421)
                  ·
                    refine ⟨2114870717750698206158477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22558620989340780865690421 2114870717750698206158477)
                    ·
                      refine ⟨793076519156511827309429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2114870717750698206158477 793076519156511827309429)
                      ·
                        rfl

theorem cell23_1544511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 5, 3].length) (baseStart_1544511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1544511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1544511 prefixEnd_1544511 := by exact prefixLift 1544511
  have htrace : WordTrace (prefixWord ++ tailWord_1544511) baseStart_1544511 baseEnd_1544511 := by
    simpa [prefixWord, tailWord_1544511, baseEnd_1544511] using wordTrace_append hprefix tailTrace_1544511
  have hstable : (prefixWord ++ tailWord_1544511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544511).length < 2 ^ (prefixWord ++ tailWord_1544511).sum := by decide
  have hdescent : baseEnd_1544511 < baseStart_1544511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544516 : List Nat := [2, 3, 4, 1, 2, 2, 2, 1, 1, 3, 2]
def baseStart_1544516 : Nat := 118140960795 + 1544516 * 2 ^ 59
def prefixEnd_1544516 : Nat := 4983230072969 + 3 ^ 40 * 1544516 * 2
def baseEnd_1544516 : Nat := 793079086559784307746907

theorem tailTrace_1544516 : CollatzResearch.WordTrace tailWord_1544516 prefixEnd_1544516 793079086559784307746907 := by
  unfold tailWord_1544516
  simp only [CollatzResearch.WordTrace]
  refine ⟨28166563236244894588562701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37555417648326526118083601 28166563236244894588562701)
  ·
    refine ⟨10562461213591835470711013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28166563236244894588562701 10562461213591835470711013)
    ·
      refine ⟨1980461477548469150758315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10562461213591835470711013 1980461477548469150758315)
      ·
        refine ⟨2970692216322703726137473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1980461477548469150758315 2970692216322703726137473)
        ·
          refine ⟨2228019162242027794603105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2970692216322703726137473 2228019162242027794603105)
          ·
            refine ⟨1671014371681520845952329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2228019162242027794603105 1671014371681520845952329)
            ·
              refine ⟨1253260778761140634464247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1671014371681520845952329 1253260778761140634464247)
              ·
                refine ⟨1879891168141710951696371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1253260778761140634464247 1879891168141710951696371)
                ·
                  refine ⟨2819836752212566427544557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1879891168141710951696371 2819836752212566427544557)
                  ·
                    refine ⟨1057438782079712410329209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2819836752212566427544557 1057438782079712410329209)
                    ·
                      refine ⟨793079086559784307746907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1057438782079712410329209 793079086559784307746907)
                      ·
                        rfl

theorem cell23_1544516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_1544516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1544516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1544516 prefixEnd_1544516 := by exact prefixLift 1544516
  have htrace : WordTrace (prefixWord ++ tailWord_1544516) baseStart_1544516 baseEnd_1544516 := by
    simpa [prefixWord, tailWord_1544516, baseEnd_1544516] using wordTrace_append hprefix tailTrace_1544516
  have hstable : (prefixWord ++ tailWord_1544516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544516).length < 2 ^ (prefixWord ++ tailWord_1544516).sum := by decide
  have hdescent : baseEnd_1544516 < baseStart_1544516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544588 : List Nat := [2, 2, 1, 2, 1, 4, 1, 1, 4, 2, 3]
def baseStart_1544588 : Nat := 118140960795 + 1544588 * 2 ^ 59
def prefixEnd_1544588 : Nat := 4983230072969 + 3 ^ 40 * 1544588 * 2
def baseEnd_1544588 : Nat := 793116057166908026046575

theorem tailTrace_1544588 : CollatzResearch.WordTrace tailWord_1544588 prefixEnd_1544588 793116057166908026046575 := by
  unfold tailWord_1544588
  simp only [CollatzResearch.WordTrace]
  refine ⟨28167876264114472736873209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37557168352152630315830945 28167876264114472736873209)
  ·
    refine ⟨21125907198085854552654907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28167876264114472736873209 21125907198085854552654907)
    ·
      refine ⟨31688860797128781828982361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21125907198085854552654907 31688860797128781828982361)
      ·
        refine ⟨23766645597846586371736771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31688860797128781828982361 23766645597846586371736771)
        ·
          refine ⟨35649968396769879557605157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23766645597846586371736771 35649968396769879557605157)
          ·
            refine ⟨6684369074394352417050967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35649968396769879557605157 6684369074394352417050967)
            ·
              refine ⟨10026553611591528625576451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6684369074394352417050967 10026553611591528625576451)
              ·
                refine ⟨15039830417387292938364677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10026553611591528625576451 15039830417387292938364677)
                ·
                  refine ⟨2819968203260117425943377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15039830417387292938364677 2819968203260117425943377)
                  ·
                    refine ⟨2114976152445088069457533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2819968203260117425943377 2114976152445088069457533)
                    ·
                      refine ⟨793116057166908026046575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2114976152445088069457533 793116057166908026046575)
                      ·
                        rfl

theorem cell23_1544588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 4, 2, 3].length) (baseStart_1544588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1544588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1544588 prefixEnd_1544588 := by exact prefixLift 1544588
  have htrace : WordTrace (prefixWord ++ tailWord_1544588) baseStart_1544588 baseEnd_1544588 := by
    simpa [prefixWord, tailWord_1544588, baseEnd_1544588] using wordTrace_append hprefix tailTrace_1544588
  have hstable : (prefixWord ++ tailWord_1544588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544588).length < 2 ^ (prefixWord ++ tailWord_1544588).sum := by decide
  have hdescent : baseEnd_1544588 < baseStart_1544588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544608 : List Nat := [2, 1, 1, 4, 1, 4, 1, 3, 6]
def baseStart_1544608 : Nat := 118140960795 + 1544608 * 2 ^ 59
def prefixEnd_1544608 : Nat := 4983230072969 + 3 ^ 40 * 1544608 * 2
def baseEnd_1544608 : Nat := 88125147419999771977387

theorem tailTrace_1544608 : CollatzResearch.WordTrace tailWord_1544608 prefixEnd_1544608 88125147419999771977387 := by
  unfold tailWord_1544608
  simp only [CollatzResearch.WordTrace]
  refine ⟨28168240994078244444737239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37557654658770992592982985 28168240994078244444737239)
  ·
    refine ⟨42252361491117366667105859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28168240994078244444737239 42252361491117366667105859)
    ·
      refine ⟨63378542236676050000658789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42252361491117366667105859 63378542236676050000658789)
      ·
        refine ⟨11883476669376759375123523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63378542236676050000658789 11883476669376759375123523)
        ·
          refine ⟨17825215004065139062685285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11883476669376759375123523 17825215004065139062685285)
          ·
            refine ⟨3342227813262213574253491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17825215004065139062685285 3342227813262213574253491)
            ·
              refine ⟨5013341719893320361380237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3342227813262213574253491 5013341719893320361380237)
              ·
                refine ⟨1880003144959995135517589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5013341719893320361380237 1880003144959995135517589)
                ·
                  refine ⟨88125147419999771977387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1880003144959995135517589 88125147419999771977387)
                  ·
                    rfl

theorem cell23_1544608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 3, 6].length) (baseStart_1544608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1544608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1544608 prefixEnd_1544608 := by exact prefixLift 1544608
  have htrace : WordTrace (prefixWord ++ tailWord_1544608) baseStart_1544608 baseEnd_1544608 := by
    simpa [prefixWord, tailWord_1544608, baseEnd_1544608] using wordTrace_append hprefix tailTrace_1544608
  have hstable : (prefixWord ++ tailWord_1544608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544608).length < 2 ^ (prefixWord ++ tailWord_1544608).sum := by decide
  have hdescent : baseEnd_1544608 < baseStart_1544608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544651 : List Nat := [1, 1, 1, 1, 3, 3, 1, 1, 5, 6]
def baseStart_1544651 : Nat := 118140960795 + 1544651 * 2 ^ 59
def prefixEnd_1544651 : Nat := 4983230072969 + 3 ^ 40 * 1544651 * 2
def baseEnd_1544651 : Nat := 264382802149380426519595

theorem tailTrace_1544651 : CollatzResearch.WordTrace tailWord_1544651 prefixEnd_1544651 264382802149380426519595 := by
  unfold tailWord_1544651
  simp only [CollatzResearch.WordTrace]
  refine ⟨56338050327000707233289807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37558700218000471488859871 56338050327000707233289807)
  ·
    refine ⟨84507075490501060849934711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56338050327000707233289807 84507075490501060849934711)
    ·
      refine ⟨126760613235751591274902067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84507075490501060849934711 126760613235751591274902067)
      ·
        refine ⟨190140919853627386912353101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126760613235751591274902067 190140919853627386912353101)
        ·
          refine ⟨71302844945110270092132413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190140919853627386912353101 71302844945110270092132413)
          ·
            refine ⟨26738566854416351284549655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71302844945110270092132413 26738566854416351284549655)
            ·
              refine ⟨40107850281624526926824483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26738566854416351284549655 40107850281624526926824483)
              ·
                refine ⟨60161775422436790390236725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40107850281624526926824483 60161775422436790390236725)
                ·
                  refine ⟨5640166445853449099084693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60161775422436790390236725 5640166445853449099084693)
                  ·
                    refine ⟨264382802149380426519595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5640166445853449099084693 264382802149380426519595)
                    ·
                      rfl

theorem cell23_1544651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5, 6].length) (baseStart_1544651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1544651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1544651 prefixEnd_1544651 := by exact prefixLift 1544651
  have htrace : WordTrace (prefixWord ++ tailWord_1544651) baseStart_1544651 baseEnd_1544651 := by
    simpa [prefixWord, tailWord_1544651, baseEnd_1544651] using wordTrace_append hprefix tailTrace_1544651
  have hstable : (prefixWord ++ tailWord_1544651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544651).length < 2 ^ (prefixWord ++ tailWord_1544651).sum := by decide
  have hdescent : baseEnd_1544651 < baseStart_1544651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544662 : List Nat := [5, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2]
def baseStart_1544662 : Nat := 118140960795 + 1544662 * 2 ^ 59
def prefixEnd_1544662 : Nat := 4983230072969 + 3 ^ 40 * 1544662 * 2
def baseEnd_1544662 : Nat := 793154054735340736521235

theorem tailTrace_1544662 : CollatzResearch.WordTrace tailWord_1544662 prefixEnd_1544662 793154054735340736521235 := by
  unfold tailWord_1544662
  simp only [CollatzResearch.WordTrace]
  refine ⟨3521153220622553506996265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37558967686640570741293493 3521153220622553506996265)
  ·
    refine ⟨2640864915466915130247199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3521153220622553506996265 2640864915466915130247199)
    ·
      refine ⟨3961297373200372695370799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2640864915466915130247199 3961297373200372695370799)
      ·
        refine ⟨5941946059800559043056199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3961297373200372695370799 5941946059800559043056199)
        ·
          refine ⟨8912919089700838564584299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5941946059800559043056199 8912919089700838564584299)
          ·
            refine ⟨13369378634551257846876449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8912919089700838564584299 13369378634551257846876449)
            ·
              refine ⟨10027033975913443385157337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13369378634551257846876449 10027033975913443385157337)
              ·
                refine ⟨7520275481935082538868003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10027033975913443385157337 7520275481935082538868003)
                ·
                  refine ⟨11280413222902623808302005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7520275481935082538868003 11280413222902623808302005)
                  ·
                    refine ⟨1057538739647120982028313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11280413222902623808302005 1057538739647120982028313)
                    ·
                      refine ⟨793154054735340736521235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1057538739647120982028313 793154054735340736521235)
                      ·
                        rfl

theorem cell23_1544662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_1544662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1544662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1544662 prefixEnd_1544662 := by exact prefixLift 1544662
  have htrace : WordTrace (prefixWord ++ tailWord_1544662) baseStart_1544662 baseEnd_1544662 := by
    simpa [prefixWord, tailWord_1544662, baseEnd_1544662] using wordTrace_append hprefix tailTrace_1544662
  have hstable : (prefixWord ++ tailWord_1544662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544662).length < 2 ^ (prefixWord ++ tailWord_1544662).sum := by decide
  have hdescent : baseEnd_1544662 < baseStart_1544662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544685 : List Nat := [1, 5, 1, 3, 1, 1, 2, 2, 1, 6]
def baseStart_1544685 : Nat := 118140960795 + 1544685 * 2 ^ 59
def prefixEnd_1544685 : Nat := 4983230072969 + 3 ^ 40 * 1544685 * 2
def baseEnd_1544685 : Nat := 264388621596798048844543

theorem tailTrace_1544685 : CollatzResearch.WordTrace tailWord_1544685 prefixEnd_1544685 264388621596798048844543 := by
  unfold tailWord_1544685
  simp only [CollatzResearch.WordTrace]
  refine ⟨56339290408877531040027509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37559526939251687360018339 56339290408877531040027509)
  ·
    refine ⟨5281808475832268535002579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56339290408877531040027509 5281808475832268535002579)
    ·
      refine ⟨7922712713748402802503869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5281808475832268535002579 7922712713748402802503869)
      ·
        refine ⟨2971017267655651050938951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7922712713748402802503869 2971017267655651050938951)
        ·
          refine ⟨4456525901483476576408427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2971017267655651050938951 4456525901483476576408427)
          ·
            refine ⟨6684788852225214864612641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4456525901483476576408427 6684788852225214864612641)
            ·
              refine ⟨5013591639168911148459481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6684788852225214864612641 5013591639168911148459481)
              ·
                refine ⟨3760193729376683361344611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5013591639168911148459481 3760193729376683361344611)
                ·
                  refine ⟨5640290594065025042016917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3760193729376683361344611 5640290594065025042016917)
                  ·
                    refine ⟨264388621596798048844543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5640290594065025042016917 264388621596798048844543)
                    ·
                      rfl

theorem cell23_1544685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_1544685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1544685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1544685 prefixEnd_1544685 := by exact prefixLift 1544685
  have htrace : WordTrace (prefixWord ++ tailWord_1544685) baseStart_1544685 baseEnd_1544685 := by
    simpa [prefixWord, tailWord_1544685, baseEnd_1544685] using wordTrace_append hprefix tailTrace_1544685
  have hstable : (prefixWord ++ tailWord_1544685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544685).length < 2 ^ (prefixWord ++ tailWord_1544685).sum := by decide
  have hdescent : baseEnd_1544685 < baseStart_1544685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544688 : List Nat := [2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 4]
def baseStart_1544688 : Nat := 118140960795 + 1544688 * 2 ^ 59
def prefixEnd_1544688 : Nat := 4983230072969 + 3 ^ 40 * 1544688 * 2
def baseEnd_1544688 : Nat := 793167405232357634796115

theorem tailTrace_1544688 : CollatzResearch.WordTrace tailWord_1544688 prefixEnd_1544688 793167405232357634796115 := by
  unfold tailWord_1544688
  simp only [CollatzResearch.WordTrace]
  refine ⟨28169699913933331276193359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37559599885244441701591145 28169699913933331276193359)
  ·
    refine ⟨42254549870899996914290039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28169699913933331276193359 42254549870899996914290039)
    ·
      refine ⟨63381824806349995371435059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42254549870899996914290039 63381824806349995371435059)
      ·
        refine ⟨95072737209524993057152589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63381824806349995371435059 95072737209524993057152589)
        ·
          refine ⟨35652276453571872396432221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95072737209524993057152589 35652276453571872396432221)
          ·
            refine ⟨13369603670089452148662083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35652276453571872396432221 13369603670089452148662083)
            ·
              refine ⟨20054405505134178222993125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13369603670089452148662083 20054405505134178222993125)
              ·
                refine ⟨3760201032212658416811211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20054405505134178222993125 3760201032212658416811211)
                ·
                  refine ⟨5640301548318987625216817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3760201032212658416811211 5640301548318987625216817)
                  ·
                    refine ⟨4230226161239240718912613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5640301548318987625216817 4230226161239240718912613)
                    ·
                      refine ⟨793167405232357634796115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4230226161239240718912613 793167405232357634796115)
                      ·
                        rfl

theorem cell23_1544688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 4].length) (baseStart_1544688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1544688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1544688 prefixEnd_1544688 := by exact prefixLift 1544688
  have htrace : WordTrace (prefixWord ++ tailWord_1544688) baseStart_1544688 baseEnd_1544688 := by
    simpa [prefixWord, tailWord_1544688, baseEnd_1544688] using wordTrace_append hprefix tailTrace_1544688
  have hstable : (prefixWord ++ tailWord_1544688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544688).length < 2 ^ (prefixWord ++ tailWord_1544688).sum := by decide
  have hdescent : baseEnd_1544688 < baseStart_1544688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544709 : List Nat := [1, 3, 1, 1, 2, 2, 4, 4, 1, 2, 2]
def baseStart_1544709 : Nat := 118140960795 + 1544709 * 2 ^ 59
def prefixEnd_1544709 : Nat := 4983230072969 + 3 ^ 40 * 1544709 * 2
def baseEnd_1544709 : Nat := 793178188326102052633519

theorem tailTrace_1544709 : CollatzResearch.WordTrace tailWord_1544709 prefixEnd_1544709 793178188326102052633519 := by
  unfold tailWord_1544709
  simp only [CollatzResearch.WordTrace]
  refine ⟨56340165760790583138901181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37560110507193722092600787 56340165760790583138901181)
  ·
    refine ⟨21127562160296468677087943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56340165760790583138901181 21127562160296468677087943)
    ·
      refine ⟨31691343240444703015631915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21127562160296468677087943 31691343240444703015631915)
      ·
        refine ⟨47537014860667054523447873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31691343240444703015631915 47537014860667054523447873)
        ·
          refine ⟨35652761145500290892585905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47537014860667054523447873 35652761145500290892585905)
          ·
            refine ⟨26739570859125218169439429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35652761145500290892585905 26739570859125218169439429)
            ·
              refine ⟨5013669536085978406769893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26739570859125218169439429 5013669536085978406769893)
              ·
                refine ⟨940063038016120951269355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5013669536085978406769893 940063038016120951269355)
                ·
                  refine ⟨1410094557024181426904033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 940063038016120951269355 1410094557024181426904033)
                  ·
                    refine ⟨1057570917768136070178025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1410094557024181426904033 1057570917768136070178025)
                    ·
                      refine ⟨793178188326102052633519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1057570917768136070178025 793178188326102052633519)
                      ·
                        rfl

theorem cell23_1544709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 4, 1, 2, 2].length) (baseStart_1544709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1544709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1544709 prefixEnd_1544709 := by exact prefixLift 1544709
  have htrace : WordTrace (prefixWord ++ tailWord_1544709) baseStart_1544709 baseEnd_1544709 := by
    simpa [prefixWord, tailWord_1544709, baseEnd_1544709] using wordTrace_append hprefix tailTrace_1544709
  have hstable : (prefixWord ++ tailWord_1544709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544709).length < 2 ^ (prefixWord ++ tailWord_1544709).sum := by decide
  have hdescent : baseEnd_1544709 < baseStart_1544709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544749 : List Nat := [1, 5, 4, 1, 1, 2, 9]
def baseStart_1544749 : Nat := 118140960795 + 1544749 * 2 ^ 59
def prefixEnd_1544749 : Nat := 4983230072969 + 3 ^ 40 * 1544749 * 2
def baseEnd_1544749 : Nat := 9792576883361504890535

theorem tailTrace_1544749 : CollatzResearch.WordTrace tailWord_1544749 prefixEnd_1544749 9792576883361504890535 := by
  unfold tailWord_1544749
  simp only [CollatzResearch.WordTrace]
  refine ⟨56341624680645669970357301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37561083120430446646904867 56341624680645669970357301)
  ·
    refine ⟨5282027313810531559720997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56341624680645669970357301 5282027313810531559720997)
    ·
      refine ⟨990380121339474667447687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5282027313810531559720997 990380121339474667447687)
      ·
        refine ⟨1485570182009212001171531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 990380121339474667447687 1485570182009212001171531)
        ·
          refine ⟨2228355273013818001757297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1485570182009212001171531 2228355273013818001757297)
          ·
            refine ⟨1671266454760363501317973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2228355273013818001757297 1671266454760363501317973)
            ·
              refine ⟨9792576883361504890535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1671266454760363501317973 9792576883361504890535)
              ·
                rfl

theorem cell23_1544749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 9].length) (baseStart_1544749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1544749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1544749 prefixEnd_1544749 := by exact prefixLift 1544749
  have htrace : WordTrace (prefixWord ++ tailWord_1544749) baseStart_1544749 baseEnd_1544749 := by
    simpa [prefixWord, tailWord_1544749, baseEnd_1544749] using wordTrace_append hprefix tailTrace_1544749
  have hstable : (prefixWord ++ tailWord_1544749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544749).length < 2 ^ (prefixWord ++ tailWord_1544749).sum := by decide
  have hdescent : baseEnd_1544749 < baseStart_1544749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544752 : List Nat := [2, 1, 1, 1, 2, 3, 4, 3, 1, 3, 2]
def baseStart_1544752 : Nat := 118140960795 + 1544752 * 2 ^ 59
def prefixEnd_1544752 : Nat := 4983230072969 + 3 ^ 40 * 1544752 * 2
def baseEnd_1544752 : Nat := 793200267994245384395821

theorem tailTrace_1544752 : CollatzResearch.WordTrace tailWord_1544752 prefixEnd_1544752 793200267994245384395821 := by
  unfold tailWord_1544752
  simp only [CollatzResearch.WordTrace]
  refine ⟨28170867049817400741358255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37561156066423200988477673 28170867049817400741358255)
  ·
    refine ⟨42256300574726101112037383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28170867049817400741358255 42256300574726101112037383)
    ·
      refine ⟨63384450862089151668056075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42256300574726101112037383 63384450862089151668056075)
      ·
        refine ⟨95076676293133727502084113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63384450862089151668056075 95076676293133727502084113)
        ·
          refine ⟨71307507219850295626563085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95076676293133727502084113 71307507219850295626563085)
          ·
            refine ⟨26740315207443860859961157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71307507219850295626563085 26740315207443860859961157)
            ·
              refine ⟨5013809101395723911242717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26740315207443860859961157 5013809101395723911242717)
              ·
                refine ⟨1880178413023396466716019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5013809101395723911242717 1880178413023396466716019)
                ·
                  refine ⟨2820267619535094700074029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1880178413023396466716019 2820267619535094700074029)
                  ·
                    refine ⟨1057600357325660512527761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2820267619535094700074029 1057600357325660512527761)
                    ·
                      refine ⟨793200267994245384395821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1057600357325660512527761 793200267994245384395821)
                      ·
                        rfl

theorem cell23_1544752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 3, 1, 3, 2].length) (baseStart_1544752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1544752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1544752 prefixEnd_1544752 := by exact prefixLift 1544752
  have htrace : WordTrace (prefixWord ++ tailWord_1544752) baseStart_1544752 baseEnd_1544752 := by
    simpa [prefixWord, tailWord_1544752, baseEnd_1544752] using wordTrace_append hprefix tailTrace_1544752
  have hstable : (prefixWord ++ tailWord_1544752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544752).length < 2 ^ (prefixWord ++ tailWord_1544752).sum := by decide
  have hdescent : baseEnd_1544752 < baseStart_1544752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544816 : List Nat := [2, 1, 1, 1, 7, 1, 2, 2, 2, 2, 2]
def baseStart_1544816 : Nat := 118140960795 + 1544816 * 2 ^ 59
def prefixEnd_1544816 : Nat := 4983230072969 + 3 ^ 40 * 1544816 * 2
def baseEnd_1544816 : Nat := 793233130756133133995527

theorem tailTrace_1544816 : CollatzResearch.WordTrace tailWord_1544816 prefixEnd_1544816 793233130756133133995527 := by
  unfold tailWord_1544816
  simp only [CollatzResearch.WordTrace]
  refine ⟨28172034185701470206523151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37562712247601960275364201 28172034185701470206523151)
  ·
    refine ⟨42258051278552205309784727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28172034185701470206523151 42258051278552205309784727)
    ·
      refine ⟨63387076917828307964677091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42258051278552205309784727 63387076917828307964677091)
      ·
        refine ⟨95080615376742461947015637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63387076917828307964677091 95080615376742461947015637)
        ·
          refine ⟨2228451922892401451883179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 95080615376742461947015637 2228451922892401451883179)
          ·
            refine ⟨3342677884338602177824769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2228451922892401451883179 3342677884338602177824769)
            ·
              refine ⟨2507008413253951633368577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3342677884338602177824769 2507008413253951633368577)
              ·
                refine ⟨1880256309940463725026433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2507008413253951633368577 1880256309940463725026433)
                ·
                  refine ⟨1410192232455347793769825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1880256309940463725026433 1410192232455347793769825)
                  ·
                    refine ⟨1057644174341510845327369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1410192232455347793769825 1057644174341510845327369)
                    ·
                      refine ⟨793233130756133133995527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1057644174341510845327369 793233130756133133995527)
                      ·
                        rfl

theorem cell23_1544816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 2, 2, 2, 2].length) (baseStart_1544816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1544816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1544816 prefixEnd_1544816 := by exact prefixLift 1544816
  have htrace : WordTrace (prefixWord ++ tailWord_1544816) baseStart_1544816 baseEnd_1544816 := by
    simpa [prefixWord, tailWord_1544816, baseEnd_1544816] using wordTrace_append hprefix tailTrace_1544816
  have hstable : (prefixWord ++ tailWord_1544816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544816).length < 2 ^ (prefixWord ++ tailWord_1544816).sum := by decide
  have hdescent : baseEnd_1544816 < baseStart_1544816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544852 : List Nat := [2, 4, 2, 2, 1, 2, 1, 1, 1, 7]
def baseStart_1544852 : Nat := 118140960795 + 1544852 * 2 ^ 59
def prefixEnd_1544852 : Nat := 4983230072969 + 3 ^ 40 * 1544852 * 2
def baseEnd_1544852 : Nat := 264417205353231664381787

theorem tailTrace_1544852 : CollatzResearch.WordTrace tailWord_1544852 prefixEnd_1544852 264417205353231664381787 := by
  unfold tailWord_1544852
  simp only [CollatzResearch.WordTrace]
  refine ⟨28172690699636259280678405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37563587599515012374237873 28172690699636259280678405)
  ·
    refine ⟨5282379506181798615127201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28172690699636259280678405 5282379506181798615127201)
    ·
      refine ⟨3961784629636348961345401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5282379506181798615127201 3961784629636348961345401)
      ·
        refine ⟨2971338472227261721009051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3961784629636348961345401 2971338472227261721009051)
        ·
          refine ⟨4457007708340892581513577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2971338472227261721009051 4457007708340892581513577)
          ·
            refine ⟨3342755781255669436135183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4457007708340892581513577 3342755781255669436135183)
            ·
              refine ⟨5014133671883504154202775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3342755781255669436135183 5014133671883504154202775)
              ·
                refine ⟨7521200507825256231304163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5014133671883504154202775 7521200507825256231304163)
                ·
                  refine ⟨11281800761737884346956245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7521200507825256231304163 11281800761737884346956245)
                  ·
                    refine ⟨264417205353231664381787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11281800761737884346956245 264417205353231664381787)
                    ·
                      rfl

theorem cell23_1544852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_1544852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1544852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1544852 prefixEnd_1544852 := by exact prefixLift 1544852
  have htrace : WordTrace (prefixWord ++ tailWord_1544852) baseStart_1544852 baseEnd_1544852 := by
    simpa [prefixWord, tailWord_1544852, baseEnd_1544852] using wordTrace_append hprefix tailTrace_1544852
  have hstable : (prefixWord ++ tailWord_1544852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544852).length < 2 ^ (prefixWord ++ tailWord_1544852).sum := by decide
  have hdescent : baseEnd_1544852 < baseStart_1544852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544855 : List Nat := [1, 1, 3, 3, 2, 1, 3, 1, 1, 3, 4]
def baseStart_1544855 : Nat := 118140960795 + 1544855 * 2 ^ 59
def prefixEnd_1544855 : Nat := 4983230072969 + 3 ^ 40 * 1544855 * 2
def baseEnd_1544855 : Nat := 793253156501658481407847

theorem tailTrace_1544855 : CollatzResearch.WordTrace tailWord_1544855 prefixEnd_1544855 793253156501658481407847 := by
  unfold tailWord_1544855
  simp only [CollatzResearch.WordTrace]
  refine ⟨56345490818261650073716019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37563660545507766715810679 56345490818261650073716019)
  ·
    refine ⟨84518236227392475110574029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56345490818261650073716019 84518236227392475110574029)
    ·
      refine ⟨31694338585272178166465261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84518236227392475110574029 31694338585272178166465261)
      ·
        refine ⟨11885376969477066812424473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31694338585272178166465261 11885376969477066812424473)
        ·
          refine ⟨8914032727107800109318355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11885376969477066812424473 8914032727107800109318355)
          ·
            refine ⟨13371049090661700163977533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8914032727107800109318355 13371049090661700163977533)
            ·
              refine ⟨5014143408998137561491575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13371049090661700163977533 5014143408998137561491575)
              ·
                refine ⟨7521215113497206342237363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5014143408998137561491575 7521215113497206342237363)
                ·
                  refine ⟨11281822670245809513356045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7521215113497206342237363 11281822670245809513356045)
                  ·
                    refine ⟨4230683501342178567508517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11281822670245809513356045 4230683501342178567508517)
                    ·
                      refine ⟨793253156501658481407847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4230683501342178567508517 793253156501658481407847)
                      ·
                        rfl

theorem cell23_1544855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_1544855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1544855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1544855 prefixEnd_1544855 := by exact prefixLift 1544855
  have htrace : WordTrace (prefixWord ++ tailWord_1544855) baseStart_1544855 baseEnd_1544855 := by
    simpa [prefixWord, tailWord_1544855, baseEnd_1544855] using wordTrace_append hprefix tailTrace_1544855
  have hstable : (prefixWord ++ tailWord_1544855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544855).length < 2 ^ (prefixWord ++ tailWord_1544855).sum := by decide
  have hdescent : baseEnd_1544855 < baseStart_1544855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544965 : List Nat := [1, 3, 1, 1, 2, 1, 1, 4, 3, 1, 5]
def baseStart_1544965 : Nat := 118140960795 + 1544965 * 2 ^ 59
def prefixEnd_1544965 : Nat := 4983230072969 + 3 ^ 40 * 1544965 * 2
def baseEnd_1544965 : Nat := 793309639373653051032341

theorem tailTrace_1544965 : CollatzResearch.WordTrace tailWord_1544965 prefixEnd_1544965 793309639373653051032341 := by
  unfold tailWord_1544965
  simp only [CollatzResearch.WordTrace]
  refine ⟨56349502847863138860220349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37566335231908759240146899 56349502847863138860220349)
  ·
    refine ⟨21131063567948677072582631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56349502847863138860220349 21131063567948677072582631)
    ·
      refine ⟨31696595351923015608873947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21131063567948677072582631 31696595351923015608873947)
      ·
        refine ⟨47544893027884523413310921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31696595351923015608873947 47544893027884523413310921)
        ·
          refine ⟨35658669770913392559983191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47544893027884523413310921 35658669770913392559983191)
          ·
            refine ⟨53488004656370088839974787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35658669770913392559983191 53488004656370088839974787)
            ·
              refine ⟨80232006984555133259962181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53488004656370088839974787 80232006984555133259962181)
              ·
                refine ⟨15043501309604087486242909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80232006984555133259962181 15043501309604087486242909)
                ·
                  refine ⟨5641312991101532807341091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15043501309604087486242909 5641312991101532807341091)
                  ·
                    refine ⟨8461969486652299211011637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5641312991101532807341091 8461969486652299211011637)
                    ·
                      refine ⟨793309639373653051032341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8461969486652299211011637 793309639373653051032341)
                      ·
                        rfl

theorem cell23_1544965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3, 1, 5].length) (baseStart_1544965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1544965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1544965 prefixEnd_1544965 := by exact prefixLift 1544965
  have htrace : WordTrace (prefixWord ++ tailWord_1544965) baseStart_1544965 baseEnd_1544965 := by
    simpa [prefixWord, tailWord_1544965, baseEnd_1544965] using wordTrace_append hprefix tailTrace_1544965
  have hstable : (prefixWord ++ tailWord_1544965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544965).length < 2 ^ (prefixWord ++ tailWord_1544965).sum := by decide
  have hdescent : baseEnd_1544965 < baseStart_1544965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544979 : List Nat := [1, 1, 1, 2, 1, 3, 7, 1, 1, 1, 4]
def baseStart_1544979 : Nat := 118140960795 + 1544979 * 2 ^ 59
def prefixEnd_1544979 : Nat := 4983230072969 + 3 ^ 40 * 1544979 * 2
def baseEnd_1544979 : Nat := 793316828102815996257277

theorem tailTrace_1544979 : CollatzResearch.WordTrace tailWord_1544979 prefixEnd_1544979 793316828102815996257277 := by
  unfold tailWord_1544979
  simp only [CollatzResearch.WordTrace]
  refine ⟨56350013469812419251229991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37566675646541612834153327 56350013469812419251229991)
  ·
    refine ⟨84525020204718628876844987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56350013469812419251229991 84525020204718628876844987)
    ·
      refine ⟨126787530307077943315267481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84525020204718628876844987 126787530307077943315267481)
      ·
        refine ⟨95090647730308457486450611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126787530307077943315267481 95090647730308457486450611)
        ·
          refine ⟨142635971595462686229675917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95090647730308457486450611 142635971595462686229675917)
          ·
            refine ⟨53488489348298507336128469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142635971595462686229675917 53488489348298507336128469)
            ·
              refine ⟨1253636469100746265690511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 53488489348298507336128469 1253636469100746265690511)
              ·
                refine ⟨1880454703651119398535767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1253636469100746265690511 1880454703651119398535767)
                ·
                  refine ⟨2820682055476679097803651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1880454703651119398535767 2820682055476679097803651)
                  ·
                    refine ⟨4231023083215018646705477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2820682055476679097803651 4231023083215018646705477)
                    ·
                      refine ⟨793316828102815996257277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4231023083215018646705477 793316828102815996257277)
                      ·
                        rfl

theorem cell23_1544979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7, 1, 1, 1, 4].length) (baseStart_1544979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1544979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1544979 prefixEnd_1544979 := by exact prefixLift 1544979
  have htrace : WordTrace (prefixWord ++ tailWord_1544979) baseStart_1544979 baseEnd_1544979 := by
    simpa [prefixWord, tailWord_1544979, baseEnd_1544979] using wordTrace_append hprefix tailTrace_1544979
  have hstable : (prefixWord ++ tailWord_1544979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544979).length < 2 ^ (prefixWord ++ tailWord_1544979).sum := by decide
  have hdescent : baseEnd_1544979 < baseStart_1544979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545006 : List Nat := [4, 1, 3, 2, 1, 1, 2, 3, 2, 4]
def baseStart_1545006 : Nat := 118140960795 + 1545006 * 2 ^ 59
def prefixEnd_1545006 : Nat := 4983230072969 + 3 ^ 40 * 1545006 * 2
def baseEnd_1545006 : Nat := 264443564026829130206551

theorem tailTrace_1545006 : CollatzResearch.WordTrace tailWord_1545006 prefixEnd_1545006 264443564026829130206551 := by
  unfold tailWord_1545006
  simp only [CollatzResearch.WordTrace]
  refine ⟨7043874780089325357807859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37567332160476401908308581 7043874780089325357807859)
  ·
    refine ⟨10565812170133988036711789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7043874780089325357807859 10565812170133988036711789)
    ·
      refine ⟨3962179563800245513766921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10565812170133988036711789 3962179563800245513766921)
      ·
        refine ⟨2971634672850184135325191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3962179563800245513766921 2971634672850184135325191)
        ·
          refine ⟨4457452009275276202987787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2971634672850184135325191 4457452009275276202987787)
          ·
            refine ⟨6686178013912914304481681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4457452009275276202987787 6686178013912914304481681)
            ·
              refine ⟨5014633510434685728361261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6686178013912914304481681 5014633510434685728361261)
              ·
                refine ⟨1880487566413007148135473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5014633510434685728361261 1880487566413007148135473)
                ·
                  refine ⟨1410365674809755361101605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1880487566413007148135473 1410365674809755361101605)
                  ·
                    refine ⟨264443564026829130206551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1410365674809755361101605 264443564026829130206551)
                    ·
                      rfl

theorem cell23_1545006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_1545006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1545006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1545006 prefixEnd_1545006 := by exact prefixLift 1545006
  have htrace : WordTrace (prefixWord ++ tailWord_1545006) baseStart_1545006 baseEnd_1545006 := by
    simpa [prefixWord, tailWord_1545006, baseEnd_1545006] using wordTrace_append hprefix tailTrace_1545006
  have hstable : (prefixWord ++ tailWord_1545006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545006).length < 2 ^ (prefixWord ++ tailWord_1545006).sum := by decide
  have hdescent : baseEnd_1545006 < baseStart_1545006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545015 : List Nat := [1, 1, 3, 1, 2, 1, 3, 2, 2, 7]
def baseStart_1545015 : Nat := 118140960795 + 1545015 * 2 ^ 59
def prefixEnd_1545015 : Nat := 4983230072969 + 3 ^ 40 * 1545015 * 2
def baseEnd_1545015 : Nat := 264445104468792618469037

theorem tailTrace_1545015 : CollatzResearch.WordTrace tailWord_1545015 prefixEnd_1545015 264445104468792618469037 := by
  unfold tailWord_1545015
  simp only [CollatzResearch.WordTrace]
  refine ⟨56351326497681997399540499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37567550998454664933026999 56351326497681997399540499)
  ·
    refine ⟨84526989746522996099310749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56351326497681997399540499 84526989746522996099310749)
    ·
      refine ⟨31697621154946123537241531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84526989746522996099310749 31697621154946123537241531)
      ·
        refine ⟨47546431732419185305862297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31697621154946123537241531 47546431732419185305862297)
        ·
          refine ⟨35659823799314388979396723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47546431732419185305862297 35659823799314388979396723)
          ·
            refine ⟨53489735698971583469095085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35659823799314388979396723 53489735698971583469095085)
            ·
              refine ⟨20058650887114343800910657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53489735698971583469095085 20058650887114343800910657)
              ·
                refine ⟨15043988165335757850682993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20058650887114343800910657 15043988165335757850682993)
                ·
                  refine ⟨11282991124001818388012245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15043988165335757850682993 11282991124001818388012245)
                  ·
                    refine ⟨264445104468792618469037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11282991124001818388012245 264445104468792618469037)
                    ·
                      rfl

theorem cell23_1545015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 7].length) (baseStart_1545015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1545015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1545015 prefixEnd_1545015 := by exact prefixLift 1545015
  have htrace : WordTrace (prefixWord ++ tailWord_1545015) baseStart_1545015 baseEnd_1545015 := by
    simpa [prefixWord, tailWord_1545015, baseEnd_1545015] using wordTrace_append hprefix tailTrace_1545015
  have hstable : (prefixWord ++ tailWord_1545015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545015).length < 2 ^ (prefixWord ++ tailWord_1545015).sum := by decide
  have hdescent : baseEnd_1545015 < baseStart_1545015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545063 : List Nat := [1, 1, 5, 1, 2, 3, 3, 1, 2, 1, 3]
def baseStart_1545063 : Nat := 118140960795 + 1545063 * 2 ^ 59
def prefixEnd_1545063 : Nat := 4983230072969 + 3 ^ 40 * 1545063 * 2
def baseEnd_1545063 : Nat := 793359960477793667606891

theorem tailTrace_1545063 : CollatzResearch.WordTrace tailWord_1545063 prefixEnd_1545063 793359960477793667606891 := by
  unfold tailWord_1545063
  simp only [CollatzResearch.WordTrace]
  refine ⟨56353077201508101597287843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37568718134338734398191895 56353077201508101597287843)
  ·
    refine ⟨84529615802262152395931765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56353077201508101597287843 84529615802262152395931765)
    ·
      refine ⟨7924651481462076787118603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84529615802262152395931765 7924651481462076787118603)
      ·
        refine ⟨11886977222193115180677905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7924651481462076787118603 11886977222193115180677905)
        ·
          refine ⟨8915232916644836385508429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11886977222193115180677905 8915232916644836385508429)
          ·
            refine ⟨3343212343741813644565661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8915232916644836385508429 3343212343741813644565661)
            ·
              refine ⟨1253704628903180116712123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3343212343741813644565661 1253704628903180116712123)
              ·
                refine ⟨1880556943354770175068185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1253704628903180116712123 1880556943354770175068185)
                ·
                  refine ⟨1410417707516077631301139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1880556943354770175068185 1410417707516077631301139)
                  ·
                    refine ⟨2115626561274116446951709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1410417707516077631301139 2115626561274116446951709)
                    ·
                      refine ⟨793359960477793667606891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2115626561274116446951709 793359960477793667606891)
                      ·
                        rfl

theorem cell23_1545063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3, 1, 2, 1, 3].length) (baseStart_1545063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1545063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1545063 prefixEnd_1545063 := by exact prefixLift 1545063
  have htrace : WordTrace (prefixWord ++ tailWord_1545063) baseStart_1545063 baseEnd_1545063 := by
    simpa [prefixWord, tailWord_1545063, baseEnd_1545063] using wordTrace_append hprefix tailTrace_1545063
  have hstable : (prefixWord ++ tailWord_1545063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545063).length < 2 ^ (prefixWord ++ tailWord_1545063).sum := by decide
  have hdescent : baseEnd_1545063 < baseStart_1545063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545072 : List Nat := [2, 1, 1, 1, 4, 1, 2, 2, 2, 4, 3]
def baseStart_1545072 : Nat := 118140960795 + 1545072 * 2 ^ 59
def prefixEnd_1545072 : Nat := 4983230072969 + 3 ^ 40 * 1545072 * 2
def baseEnd_1545072 : Nat := 793364581803684132394349

theorem tailTrace_1545072 : CollatzResearch.WordTrace tailWord_1545072 prefixEnd_1545072 793364581803684132394349 := by
  unfold tailWord_1545072
  simp only [CollatzResearch.WordTrace]
  refine ⟨28176702729237748067182735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37568936972316997422910313 28176702729237748067182735)
  ·
    refine ⟨42265054093856622100774103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28176702729237748067182735 42265054093856622100774103)
    ·
      refine ⟨63397581140784933151161155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42265054093856622100774103 63397581140784933151161155)
      ·
        refine ⟨95096371711177399726741733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63397581140784933151161155 95096371711177399726741733)
        ·
          refine ⟨17830569695845762448764075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95096371711177399726741733 17830569695845762448764075)
          ·
            refine ⟨26745854543768643673146113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17830569695845762448764075 26745854543768643673146113)
            ·
              refine ⟨20059390907826482754859585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26745854543768643673146113 20059390907826482754859585)
              ·
                refine ⟨15044543180869862066144689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20059390907826482754859585 15044543180869862066144689)
                ·
                  refine ⟨11283407385652396549608517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15044543180869862066144689 11283407385652396549608517)
                  ·
                    refine ⟨2115638884809824353051597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11283407385652396549608517 2115638884809824353051597)
                    ·
                      refine ⟨793364581803684132394349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2115638884809824353051597 793364581803684132394349)
                      ·
                        rfl

theorem cell23_1545072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4, 3].length) (baseStart_1545072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1545072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1545072 prefixEnd_1545072 := by exact prefixLift 1545072
  have htrace : WordTrace (prefixWord ++ tailWord_1545072) baseStart_1545072 baseEnd_1545072 := by
    simpa [prefixWord, tailWord_1545072, baseEnd_1545072] using wordTrace_append hprefix tailTrace_1545072
  have hstable : (prefixWord ++ tailWord_1545072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545072).length < 2 ^ (prefixWord ++ tailWord_1545072).sum := by decide
  have hdescent : baseEnd_1545072 < baseStart_1545072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545109 : List Nat := [1, 3, 2, 1, 1, 6, 1, 1, 7]
def baseStart_1545109 : Nat := 118140960795 + 1545109 * 2 ^ 59
def prefixEnd_1545109 : Nat := 4983230072969 + 3 ^ 40 * 1545109 * 2
def baseEnd_1545109 : Nat := 88153731176433387514631

theorem tailTrace_1545109 : CollatzResearch.WordTrace tailWord_1545109 prefixEnd_1545109 88153731176433387514631 := by
  unfold tailWord_1545109
  simp only [CollatzResearch.WordTrace]
  refine ⟨56354754959341451453462381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37569836639560967635641587 56354754959341451453462381)
  ·
    refine ⟨21133033109753044295048393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56354754959341451453462381 21133033109753044295048393)
    ·
      refine ⟨15849774832314783221286295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21133033109753044295048393 15849774832314783221286295)
      ·
        refine ⟨23774662248472174831929443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15849774832314783221286295 23774662248472174831929443)
        ·
          refine ⟨35661993372708262247894165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23774662248472174831929443 35661993372708262247894165)
          ·
            refine ⟨1671655939345699792870039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 35661993372708262247894165 1671655939345699792870039)
            ·
              refine ⟨2507483909018549689305059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1671655939345699792870039 2507483909018549689305059)
              ·
                refine ⟨3761225863527824533957589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2507483909018549689305059 3761225863527824533957589)
                ·
                  refine ⟨88153731176433387514631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3761225863527824533957589 88153731176433387514631)
                  ·
                    rfl

theorem cell23_1545109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 1, 7].length) (baseStart_1545109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1545109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1545109 prefixEnd_1545109 := by exact prefixLift 1545109
  have htrace : WordTrace (prefixWord ++ tailWord_1545109) baseStart_1545109 baseEnd_1545109 := by
    simpa [prefixWord, tailWord_1545109, baseEnd_1545109] using wordTrace_append hprefix tailTrace_1545109
  have hstable : (prefixWord ++ tailWord_1545109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545109).length < 2 ^ (prefixWord ++ tailWord_1545109).sum := by decide
  have hdescent : baseEnd_1545109 < baseStart_1545109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545159 : List Nat := [1, 1, 4, 1, 1, 2, 4, 2, 2, 1, 4]
def baseStart_1545159 : Nat := 118140960795 + 1545159 * 2 ^ 59
def prefixEnd_1545159 : Nat := 4983230072969 + 3 ^ 40 * 1545159 * 2
def baseEnd_1545159 : Nat := 793409254620625292006449

theorem tailTrace_1545159 : CollatzResearch.WordTrace tailWord_1545159 prefixEnd_1545159 793409254620625292006449 := by
  unfold tailWord_1545159
  simp only [CollatzResearch.WordTrace]
  refine ⟨56356578609160309992782531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37571052406106873328521687 56356578609160309992782531)
  ·
    refine ⟨84534867913740464989173797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56356578609160309992782531 84534867913740464989173797)
    ·
      refine ⟨15850287733826337185470087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84534867913740464989173797 15850287733826337185470087)
      ·
        refine ⟨23775431600739505778205131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15850287733826337185470087 23775431600739505778205131)
        ·
          refine ⟨35663147401109258667307697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23775431600739505778205131 35663147401109258667307697)
          ·
            refine ⟨26747360550831944000480773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35663147401109258667307697 26747360550831944000480773)
            ·
              refine ⟨5015130103280989500090145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26747360550831944000480773 5015130103280989500090145)
              ·
                refine ⟨3761347577460742125067609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5015130103280989500090145 3761347577460742125067609)
                ·
                  refine ⟨2821010683095556593800707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3761347577460742125067609 2821010683095556593800707)
                  ·
                    refine ⟨4231516024643334890701061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2821010683095556593800707 4231516024643334890701061)
                    ·
                      refine ⟨793409254620625292006449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4231516024643334890701061 793409254620625292006449)
                      ·
                        rfl

theorem cell23_1545159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 2, 2, 1, 4].length) (baseStart_1545159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1545159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1545159 prefixEnd_1545159 := by exact prefixLift 1545159
  have htrace : WordTrace (prefixWord ++ tailWord_1545159) baseStart_1545159 baseEnd_1545159 := by
    simpa [prefixWord, tailWord_1545159, baseEnd_1545159] using wordTrace_append hprefix tailTrace_1545159
  have hstable : (prefixWord ++ tailWord_1545159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545159).length < 2 ^ (prefixWord ++ tailWord_1545159).sum := by decide
  have hdescent : baseEnd_1545159 < baseStart_1545159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545160 : List Nat := [2, 1, 3, 1, 6, 1, 2, 2, 5]
def baseStart_1545160 : Nat := 118140960795 + 1545160 * 2 ^ 59
def prefixEnd_1545160 : Nat := 4983230072969 + 3 ^ 40 * 1545160 * 2
def baseEnd_1545160 : Nat := 88156640900142198677105

theorem tailTrace_1545160 : CollatzResearch.WordTrace tailWord_1545160 prefixEnd_1545160 88156640900142198677105 := by
  unfold tailWord_1545160
  simp only [CollatzResearch.WordTrace]
  refine ⟨28178307541078343581784467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37571076721437791442379289 28178307541078343581784467)
  ·
    refine ⟨42267461311617515372676701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28178307541078343581784467 42267461311617515372676701)
    ·
      refine ⟨15850297991856568264753763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42267461311617515372676701 15850297991856568264753763)
      ·
        refine ⟨23775446987784852397130645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15850297991856568264753763 23775446987784852397130645)
        ·
          refine ⟨1114474077552414956115499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23775446987784852397130645 1114474077552414956115499)
          ·
            refine ⟨1671711116328622434173249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1114474077552414956115499 1671711116328622434173249)
            ·
              refine ⟨1253783337246466825629937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1671711116328622434173249 1253783337246466825629937)
              ·
                refine ⟨940337502934850119222453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1253783337246466825629937 940337502934850119222453)
                ·
                  refine ⟨88156640900142198677105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 940337502934850119222453 88156640900142198677105)
                  ·
                    rfl

theorem cell23_1545160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 2, 2, 5].length) (baseStart_1545160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1545160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1545160 prefixEnd_1545160 := by exact prefixLift 1545160
  have htrace : WordTrace (prefixWord ++ tailWord_1545160) baseStart_1545160 baseEnd_1545160 := by
    simpa [prefixWord, tailWord_1545160, baseEnd_1545160] using wordTrace_append hprefix tailTrace_1545160
  have hstable : (prefixWord ++ tailWord_1545160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545160).length < 2 ^ (prefixWord ++ tailWord_1545160).sum := by decide
  have hdescent : baseEnd_1545160 < baseStart_1545160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545162 : List Nat := [3, 1, 2, 1, 2, 1, 1, 1, 1, 5, 5]
def baseStart_1545162 : Nat := 118140960795 + 1545162 * 2 ^ 59
def prefixEnd_1545162 : Nat := 4983230072969 + 3 ^ 40 * 1545162 * 2
def baseEnd_1545162 : Nat := 793410795062588780268935

theorem tailTrace_1545162 : CollatzResearch.WordTrace tailWord_1545162 prefixEnd_1545162 793410795062588780268935 := by
  unfold tailWord_1545162
  simp only [CollatzResearch.WordTrace]
  refine ⟨14089172007037360376285435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37571125352099627670094493 14089172007037360376285435)
  ·
    refine ⟨21133758010556040564428153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14089172007037360376285435 21133758010556040564428153)
    ·
      refine ⟨15850318507917030423321115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21133758010556040564428153 15850318507917030423321115)
      ·
        refine ⟨23775477761875545634981673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15850318507917030423321115 23775477761875545634981673)
        ·
          refine ⟨17831608321406659226236255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23775477761875545634981673 17831608321406659226236255)
          ·
            refine ⟨26747412482109988839354383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17831608321406659226236255 26747412482109988839354383)
            ·
              refine ⟨40121118723164983259031575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26747412482109988839354383 40121118723164983259031575)
              ·
                refine ⟨60181678084747474888547363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40121118723164983259031575 60181678084747474888547363)
                ·
                  refine ⟨90272517127121212332821045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60181678084747474888547363 90272517127121212332821045)
                  ·
                    refine ⟨8463048480667613656201973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 90272517127121212332821045 8463048480667613656201973)
                    ·
                      refine ⟨793410795062588780268935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8463048480667613656201973 793410795062588780268935)
                      ·
                        rfl

theorem cell23_1545162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_1545162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1545162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1545162 prefixEnd_1545162 := by exact prefixLift 1545162
  have htrace : WordTrace (prefixWord ++ tailWord_1545162) baseStart_1545162 baseEnd_1545162 := by
    simpa [prefixWord, tailWord_1545162, baseEnd_1545162] using wordTrace_append hprefix tailTrace_1545162
  have hstable : (prefixWord ++ tailWord_1545162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545162).length < 2 ^ (prefixWord ++ tailWord_1545162).sum := by decide
  have hdescent : baseEnd_1545162 < baseStart_1545162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545169 : List Nat := [1, 2, 2, 1, 2, 1, 4, 3, 3, 4]
def baseStart_1545169 : Nat := 118140960795 + 1545169 * 2 ^ 59
def prefixEnd_1545169 : Nat := 4983230072969 + 3 ^ 40 * 1545169 * 2
def baseEnd_1545169 : Nat := 264471463142390084293801

theorem tailTrace_1545169 : CollatzResearch.WordTrace tailWord_1545169 prefixEnd_1545169 264471463142390084293801 := by
  unfold tailWord_1545169
  simp only [CollatzResearch.WordTrace]
  refine ⟨56356943339124081700646561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37571295559416054467097707 56356943339124081700646561)
  ·
    refine ⟨42267707504343061275484921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56356943339124081700646561 42267707504343061275484921)
    ·
      refine ⟨31700780628257295956613691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42267707504343061275484921 31700780628257295956613691)
      ·
        refine ⟨47551170942385943934920537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31700780628257295956613691 47551170942385943934920537)
        ·
          refine ⟨35663378206789457951190403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47551170942385943934920537 35663378206789457951190403)
          ·
            refine ⟨53495067310184186926785605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35663378206789457951190403 53495067310184186926785605)
            ·
              refine ⟨10030325120659535048772301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53495067310184186926785605 10030325120659535048772301)
              ·
                refine ⟨3761371920247325643289613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10030325120659535048772301 3761371920247325643289613)
                ·
                  refine ⟨1410514470092747116233605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3761371920247325643289613 1410514470092747116233605)
                  ·
                    refine ⟨264471463142390084293801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1410514470092747116233605 264471463142390084293801)
                    ·
                      rfl

theorem cell23_1545169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3, 3, 4].length) (baseStart_1545169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1545169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1545169 prefixEnd_1545169 := by exact prefixLift 1545169
  have htrace : WordTrace (prefixWord ++ tailWord_1545169) baseStart_1545169 baseEnd_1545169 := by
    simpa [prefixWord, tailWord_1545169, baseEnd_1545169] using wordTrace_append hprefix tailTrace_1545169
  have hstable : (prefixWord ++ tailWord_1545169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545169).length < 2 ^ (prefixWord ++ tailWord_1545169).sum := by decide
  have hdescent : baseEnd_1545169 < baseStart_1545169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545176 : List Nat := [2, 1, 2, 2, 2, 4, 1, 1, 2, 4, 2]
def baseStart_1545176 : Nat := 118140960795 + 1545176 * 2 ^ 59
def prefixEnd_1545176 : Nat := 4983230072969 + 3 ^ 40 * 1545176 * 2
def baseEnd_1545176 : Nat := 793417983791751725493871

theorem tailTrace_1545176 : CollatzResearch.WordTrace tailWord_1545176 prefixEnd_1545176 793417983791751725493871 := by
  unfold tailWord_1545176
  simp only [CollatzResearch.WordTrace]
  refine ⟨28178599325049360948075691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37571465766732481264100921 28178599325049360948075691)
  ·
    refine ⟨42267898987574041422113537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28178599325049360948075691 42267898987574041422113537)
    ·
      refine ⟨31700924240680531066585153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42267898987574041422113537 31700924240680531066585153)
      ·
        refine ⟨23775693180510398299938865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31700924240680531066585153 23775693180510398299938865)
        ·
          refine ⟨17831769885382798724954149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23775693180510398299938865 17831769885382798724954149)
          ·
            refine ⟨3343456853509274760928903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17831769885382798724954149 3343456853509274760928903)
            ·
              refine ⟨5015185280263912141393355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3343456853509274760928903 5015185280263912141393355)
              ·
                refine ⟨7522777920395868212090033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5015185280263912141393355 7522777920395868212090033)
                ·
                  refine ⟨5642083440296901159067525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7522777920395868212090033 5642083440296901159067525)
                  ·
                    refine ⟨1057890645055668967325161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5642083440296901159067525 1057890645055668967325161)
                    ·
                      refine ⟨793417983791751725493871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1057890645055668967325161 793417983791751725493871)
                      ·
                        rfl

theorem cell23_1545176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 2, 4, 2].length) (baseStart_1545176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1545176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1545176 prefixEnd_1545176 := by exact prefixLift 1545176
  have htrace : WordTrace (prefixWord ++ tailWord_1545176) baseStart_1545176 baseEnd_1545176 := by
    simpa [prefixWord, tailWord_1545176, baseEnd_1545176] using wordTrace_append hprefix tailTrace_1545176
  have hstable : (prefixWord ++ tailWord_1545176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545176).length < 2 ^ (prefixWord ++ tailWord_1545176).sum := by decide
  have hdescent : baseEnd_1545176 < baseStart_1545176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545259 : List Nat := [1, 1, 1, 1, 2, 1, 5, 1, 6, 4]
def baseStart_1545259 : Nat := 118140960795 + 1545259 * 2 ^ 59
def prefixEnd_1545259 : Nat := 4983230072969 + 3 ^ 40 * 1545259 * 2
def baseEnd_1545259 : Nat := 264486867562024966918663

theorem tailTrace_1545259 : CollatzResearch.WordTrace tailWord_1545259 prefixEnd_1545259 264486867562024966918663 := by
  unfold tailWord_1545259
  simp only [CollatzResearch.WordTrace]
  refine ⟨56360225908798027071422831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37573483939198684714281887 56360225908798027071422831)
  ·
    refine ⟨84540338863197040607134247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56360225908798027071422831 84540338863197040607134247)
    ·
      refine ⟨126810508294795560910701371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84540338863197040607134247 126810508294795560910701371)
      ·
        refine ⟨190215762442193341366052057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126810508294795560910701371 190215762442193341366052057)
        ·
          refine ⟨142661821831645006024539043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190215762442193341366052057 142661821831645006024539043)
          ·
            refine ⟨213992732747467509036808565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142661821831645006024539043 213992732747467509036808565)
            ·
              refine ⟨20061818695075078972200803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 213992732747467509036808565 20061818695075078972200803)
              ·
                refine ⟨30092728042612618458301205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20061818695075078972200803 30092728042612618458301205)
                ·
                  refine ⟨1410596626997466490232869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 30092728042612618458301205 1410596626997466490232869)
                  ·
                    refine ⟨264486867562024966918663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1410596626997466490232869 264486867562024966918663)
                    ·
                      rfl

theorem cell23_1545259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 6, 4].length) (baseStart_1545259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1545259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1545259 prefixEnd_1545259 := by exact prefixLift 1545259
  have htrace : WordTrace (prefixWord ++ tailWord_1545259) baseStart_1545259 baseEnd_1545259 := by
    simpa [prefixWord, tailWord_1545259, baseEnd_1545259] using wordTrace_append hprefix tailTrace_1545259
  have hstable : (prefixWord ++ tailWord_1545259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545259).length < 2 ^ (prefixWord ++ tailWord_1545259).sum := by decide
  have hdescent : baseEnd_1545259 < baseStart_1545259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545266 : List Nat := [3, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4]
def baseStart_1545266 : Nat := 118140960795 + 1545266 * 2 ^ 59
def prefixEnd_1545266 : Nat := 4983230072969 + 3 ^ 40 * 1545266 * 2
def baseEnd_1545266 : Nat := 793464197050656373368457

theorem tailTrace_1545266 : CollatzResearch.WordTrace tailWord_1545266 prefixEnd_1545266 793464197050656373368457 := by
  unfold tailWord_1545266
  simp only [CollatzResearch.WordTrace]
  refine ⟨14090120304943166816731913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37573654146515111511285101 14090120304943166816731913)
  ·
    refine ⟨10567590228707375112548935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14090120304943166816731913 10567590228707375112548935)
    ·
      refine ⟨15851385343061062668823403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10567590228707375112548935 15851385343061062668823403)
      ·
        refine ⟨23777078014591594003235105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15851385343061062668823403 23777078014591594003235105)
        ·
          refine ⟨17832808510943695502426329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23777078014591594003235105 17832808510943695502426329)
          ·
            refine ⟨13374606383207771626819747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17832808510943695502426329 13374606383207771626819747)
            ·
              refine ⟨20061909574811657440229621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13374606383207771626819747 20061909574811657440229621)
              ·
                refine ⟨1880804022638592885021527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20061909574811657440229621 1880804022638592885021527)
                ·
                  refine ⟨2821206033957889327532291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1880804022638592885021527 2821206033957889327532291)
                  ·
                    refine ⟨4231809050936833991298437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2821206033957889327532291 4231809050936833991298437)
                    ·
                      refine ⟨793464197050656373368457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4231809050936833991298437 793464197050656373368457)
                      ·
                        rfl

theorem cell23_1545266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4].length) (baseStart_1545266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1545266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1545266 prefixEnd_1545266 := by exact prefixLift 1545266
  have htrace : WordTrace (prefixWord ++ tailWord_1545266) baseStart_1545266 baseEnd_1545266 := by
    simpa [prefixWord, tailWord_1545266, baseEnd_1545266] using wordTrace_append hprefix tailTrace_1545266
  have hstable : (prefixWord ++ tailWord_1545266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545266).length < 2 ^ (prefixWord ++ tailWord_1545266).sum := by decide
  have hdescent : baseEnd_1545266 < baseStart_1545266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545270 : List Nat := [5, 1, 2, 1, 1, 3, 1, 2, 2, 3, 2]
def baseStart_1545270 : Nat := 118140960795 + 1545270 * 2 ^ 59
def prefixEnd_1545270 : Nat := 4983230072969 + 3 ^ 40 * 1545270 * 2
def baseEnd_1545270 : Nat := 793466250973274357718439

theorem tailTrace_1545270 : CollatzResearch.WordTrace tailWord_1545270 prefixEnd_1545270 793466250973274357718439 := by
  unfold tailWord_1545270
  simp only [CollatzResearch.WordTrace]
  refine ⟨3522539194484885996879579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37573751407838783966715509 3522539194484885996879579)
  ·
    refine ⟨5283808791727328995319369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3522539194484885996879579 5283808791727328995319369)
    ·
      refine ⟨3962856593795496746489527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5283808791727328995319369 3962856593795496746489527)
      ·
        refine ⟨5944284890693245119734291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3962856593795496746489527 5944284890693245119734291)
        ·
          refine ⟨8916427336039867679601437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5944284890693245119734291 8916427336039867679601437)
          ·
            refine ⟨3343660251014950379850539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8916427336039867679601437 3343660251014950379850539)
            ·
              refine ⟨5015490376522425569775809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3343660251014950379850539 5015490376522425569775809)
              ·
                refine ⟨3761617782391819177331857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5015490376522425569775809 3761617782391819177331857)
                ·
                  refine ⟨2821213336793864382998893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3761617782391819177331857 2821213336793864382998893)
                  ·
                    refine ⟨1057955001297699143624585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2821213336793864382998893 1057955001297699143624585)
                    ·
                      refine ⟨793466250973274357718439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1057955001297699143624585 793466250973274357718439)
                      ·
                        rfl

theorem cell23_1545270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_1545270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1545270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1545270 prefixEnd_1545270 := by exact prefixLift 1545270
  have htrace : WordTrace (prefixWord ++ tailWord_1545270) baseStart_1545270 baseEnd_1545270 := by
    simpa [prefixWord, tailWord_1545270, baseEnd_1545270] using wordTrace_append hprefix tailTrace_1545270
  have hstable : (prefixWord ++ tailWord_1545270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545270).length < 2 ^ (prefixWord ++ tailWord_1545270).sum := by decide
  have hdescent : baseEnd_1545270 < baseStart_1545270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545276 : List Nat := [2, 2, 2, 2, 2, 2, 2, 1, 4, 4]
def baseStart_1545276 : Nat := 118140960795 + 1545276 * 2 ^ 59
def prefixEnd_1545276 : Nat := 4983230072969 + 3 ^ 40 * 1545276 * 2
def baseEnd_1545276 : Nat := 264489777285733778081137

theorem tailTrace_1545276 : CollatzResearch.WordTrace tailWord_1545276 prefixEnd_1545276 264489777285733778081137 := by
  unfold tailWord_1545276
  simp only [CollatzResearch.WordTrace]
  refine ⟨28180422974868219487395841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37573897299824292649861121 28180422974868219487395841)
  ·
    refine ⟨21135317231151164615546881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28180422974868219487395841 21135317231151164615546881)
    ·
      refine ⟨15851487923363373461660161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21135317231151164615546881 15851487923363373461660161)
      ·
        refine ⟨11888615942522530096245121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15851487923363373461660161 11888615942522530096245121)
        ·
          refine ⟨8916461956891897572183841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11888615942522530096245121 8916461956891897572183841)
          ·
            refine ⟨6687346467668923179137881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8916461956891897572183841 6687346467668923179137881)
            ·
              refine ⟨5015509850751692384353411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6687346467668923179137881 5015509850751692384353411)
              ·
                refine ⟨7523264776127538576530117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5015509850751692384353411 7523264776127538576530117)
                ·
                  refine ⟨1410612145523913483099397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7523264776127538576530117 1410612145523913483099397)
                  ·
                    refine ⟨264489777285733778081137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1410612145523913483099397 264489777285733778081137)
                    ·
                      rfl

theorem cell23_1545276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 4, 4].length) (baseStart_1545276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1545276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1545276 prefixEnd_1545276 := by exact prefixLift 1545276
  have htrace : WordTrace (prefixWord ++ tailWord_1545276) baseStart_1545276 baseEnd_1545276 := by
    simpa [prefixWord, tailWord_1545276, baseEnd_1545276] using wordTrace_append hprefix tailTrace_1545276
  have hstable : (prefixWord ++ tailWord_1545276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545276).length < 2 ^ (prefixWord ++ tailWord_1545276).sum := by decide
  have hdescent : baseEnd_1545276 < baseStart_1545276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545277 : List Nat := [1, 4, 1, 3, 1, 3, 3, 2, 1, 1, 3]
def baseStart_1545277 : Nat := 118140960795 + 1545277 * 2 ^ 59
def prefixEnd_1545277 : Nat := 4983230072969 + 3 ^ 40 * 1545277 * 2
def baseEnd_1545277 : Nat := 793469845337855830330907

theorem tailTrace_1545277 : CollatzResearch.WordTrace tailWord_1545277 prefixEnd_1545277 793469845337855830330907 := by
  unfold tailWord_1545277
  simp only [CollatzResearch.WordTrace]
  refine ⟨56360882422732816145578085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37573921615155210763718723 56360882422732816145578085)
  ·
    refine ⟨10567665454262403027295891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56360882422732816145578085 10567665454262403027295891)
    ·
      refine ⟨15851498181393604540943837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10567665454262403027295891 15851498181393604540943837)
      ·
        refine ⟨5944311818022601702853939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15851498181393604540943837 5944311818022601702853939)
        ·
          refine ⟨8916467727033902554280909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5944311818022601702853939 8916467727033902554280909)
          ·
            refine ⟨3343675397637713457855341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8916467727033902554280909 3343675397637713457855341)
            ·
              refine ⟨1253878274114142546695753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3343675397637713457855341 1253878274114142546695753)
              ·
                refine ⟨940408705585606910021815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1253878274114142546695753 940408705585606910021815)
                ·
                  refine ⟨1410613058378410365032723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 940408705585606910021815 1410613058378410365032723)
                  ·
                    refine ⟨2115919587567615547549085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1410613058378410365032723 2115919587567615547549085)
                    ·
                      refine ⟨793469845337855830330907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2115919587567615547549085 793469845337855830330907)
                      ·
                        rfl

theorem cell23_1545277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_1545277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1545277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1545277 prefixEnd_1545277 := by exact prefixLift 1545277
  have htrace : WordTrace (prefixWord ++ tailWord_1545277) baseStart_1545277 baseEnd_1545277 := by
    simpa [prefixWord, tailWord_1545277, baseEnd_1545277] using wordTrace_append hprefix tailTrace_1545277
  have hstable : (prefixWord ++ tailWord_1545277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545277).length < 2 ^ (prefixWord ++ tailWord_1545277).sum := by decide
  have hdescent : baseEnd_1545277 < baseStart_1545277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545310 : List Nat := [4, 4, 1, 1, 1, 2, 1, 2, 1, 6]
def baseStart_1545310 : Nat := 118140960795 + 1545310 * 2 ^ 59
def prefixEnd_1545310 : Nat := 4983230072969 + 3 ^ 40 * 1545310 * 2
def baseEnd_1545310 : Nat := 264495596733151400406085

theorem tailTrace_1545310 : CollatzResearch.WordTrace tailWord_1545310 prefixEnd_1545310 264495596733151400406085 := by
  unfold tailWord_1545310
  simp only [CollatzResearch.WordTrace]
  refine ⟨7045260753951657847691173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37574724021075508521019589 7045260753951657847691173)
  ·
    refine ⟨1320986391365935846442095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7045260753951657847691173 1320986391365935846442095)
    ·
      refine ⟨1981479587048903769663143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1320986391365935846442095 1981479587048903769663143)
      ·
        refine ⟨2972219380573355654494715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1981479587048903769663143 2972219380573355654494715)
        ·
          refine ⟨4458329070860033481742073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2972219380573355654494715 4458329070860033481742073)
          ·
            refine ⟨3343746803145025111306555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4458329070860033481742073 3343746803145025111306555)
            ·
              refine ⟨5015620204717537666959833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3343746803145025111306555 5015620204717537666959833)
              ·
                refine ⟨3761715153538153250219875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5015620204717537666959833 3761715153538153250219875)
                ·
                  refine ⟨5642572730307229875329813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3761715153538153250219875 5642572730307229875329813)
                  ·
                    refine ⟨264495596733151400406085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5642572730307229875329813 264495596733151400406085)
                    ·
                      rfl

theorem cell23_1545310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_1545310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1545310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1545310 prefixEnd_1545310 := by exact prefixLift 1545310
  have htrace : WordTrace (prefixWord ++ tailWord_1545310) baseStart_1545310 baseEnd_1545310 := by
    simpa [prefixWord, tailWord_1545310, baseEnd_1545310] using wordTrace_append hprefix tailTrace_1545310
  have hstable : (prefixWord ++ tailWord_1545310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545310).length < 2 ^ (prefixWord ++ tailWord_1545310).sum := by decide
  have hdescent : baseEnd_1545310 < baseStart_1545310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545320 : List Nat := [2, 1, 4, 4, 1, 2, 1, 1, 1, 1, 5]
def baseStart_1545320 : Nat := 118140960795 + 1545320 * 2 ^ 59
def prefixEnd_1545320 : Nat := 4983230072969 + 3 ^ 40 * 1545320 * 2
def baseEnd_1545320 : Nat := 793491925005999162093209

theorem tailTrace_1545320 : CollatzResearch.WordTrace tailWord_1545320 prefixEnd_1545320 793491925005999162093209 := by
  unfold tailWord_1545320
  simp only [CollatzResearch.WordTrace]
  refine ⟨28181225380788517244696707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37574967174384689659595609 28181225380788517244696707)
  ·
    refine ⟨42271838071182775867045061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28181225380788517244696707 42271838071182775867045061)
    ·
      refine ⟨7925969638346770475070949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42271838071182775867045061 7925969638346770475070949)
      ·
        refine ⟨1486119307190019464075803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7925969638346770475070949 1486119307190019464075803)
        ·
          refine ⟨2229178960785029196113705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1486119307190019464075803 2229178960785029196113705)
          ·
            refine ⟨1671884220588771897085279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2229178960785029196113705 1671884220588771897085279)
            ·
              refine ⟨2507826330883157845627919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1671884220588771897085279 2507826330883157845627919)
              ·
                refine ⟨3761739496324736768441879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2507826330883157845627919 3761739496324736768441879)
                ·
                  refine ⟨5642609244487105152662819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3761739496324736768441879 5642609244487105152662819)
                  ·
                    refine ⟨8463913866730657728994229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5642609244487105152662819 8463913866730657728994229)
                    ·
                      refine ⟨793491925005999162093209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8463913866730657728994229 793491925005999162093209)
                      ·
                        rfl

theorem cell23_1545320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_1545320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1545320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1545320 prefixEnd_1545320 := by exact prefixLift 1545320
  have htrace : WordTrace (prefixWord ++ tailWord_1545320) baseStart_1545320 baseEnd_1545320 := by
    simpa [prefixWord, tailWord_1545320, baseEnd_1545320] using wordTrace_append hprefix tailTrace_1545320
  have hstable : (prefixWord ++ tailWord_1545320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545320).length < 2 ^ (prefixWord ++ tailWord_1545320).sum := by decide
  have hdescent : baseEnd_1545320 < baseStart_1545320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545373 : List Nat := [1, 4, 2, 1, 1, 2, 1, 4, 1, 4, 2]
def baseStart_1545373 : Nat := 118140960795 + 1545373 * 2 ^ 59
def prefixEnd_1545373 : Nat := 4983230072969 + 3 ^ 40 * 1545373 * 2
def baseEnd_1545373 : Nat := 793519139480687454730465

theorem tailTrace_1545373 : CollatzResearch.WordTrace tailWord_1545373 prefixEnd_1545373 793519139480687454730465 := by
  unfold tailWord_1545373
  simp only [CollatzResearch.WordTrace]
  refine ⟨56364383830385024541072773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37576255886923349694048515 56364383830385024541072773)
  ·
    refine ⟨10568321968197192101451145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56364383830385024541072773 10568321968197192101451145)
    ·
      refine ⟨7926241476147894076088359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10568321968197192101451145 7926241476147894076088359)
      ·
        refine ⟨11889362214221841114132539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7926241476147894076088359 11889362214221841114132539)
        ·
          refine ⟨17834043321332761671198809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11889362214221841114132539 17834043321332761671198809)
          ·
            refine ⟨13375532490999571253399107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17834043321332761671198809 13375532490999571253399107)
            ·
              refine ⟨20063298736499356880098661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13375532490999571253399107 20063298736499356880098661)
              ·
                refine ⟨3761868513093629415018499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20063298736499356880098661 3761868513093629415018499)
                ·
                  refine ⟨5642802769640444122527749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3761868513093629415018499 5642802769640444122527749)
                  ·
                    refine ⟨1058025519307583272973953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5642802769640444122527749 1058025519307583272973953)
                    ·
                      refine ⟨793519139480687454730465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1058025519307583272973953 793519139480687454730465)
                      ·
                        rfl

theorem cell23_1545373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 4, 1, 4, 2].length) (baseStart_1545373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1545373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1545373 prefixEnd_1545373 := by exact prefixLift 1545373
  have htrace : WordTrace (prefixWord ++ tailWord_1545373) baseStart_1545373 baseEnd_1545373 := by
    simpa [prefixWord, tailWord_1545373, baseEnd_1545373] using wordTrace_append hprefix tailTrace_1545373
  have hstable : (prefixWord ++ tailWord_1545373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545373).length < 2 ^ (prefixWord ++ tailWord_1545373).sum := by decide
  have hdescent : baseEnd_1545373 < baseStart_1545373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545419 : List Nat := [1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 7]
def baseStart_1545419 : Nat := 118140960795 + 1545419 * 2 ^ 59
def prefixEnd_1545419 : Nat := 4983230072969 + 3 ^ 40 * 1545419 * 2
def baseEnd_1545419 : Nat := 793542759590794274755253

theorem tailTrace_1545419 : CollatzResearch.WordTrace tailWord_1545419 prefixEnd_1545419 793542759590794274755253 := by
  unfold tailWord_1545419
  simp only [CollatzResearch.WordTrace]
  refine ⟨56366061588218374397247311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37577374392145582931498207 56366061588218374397247311)
  ·
    refine ⟨84549092382327561595870967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56366061588218374397247311 84549092382327561595870967)
    ·
      refine ⟨126823638573491342393806451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84549092382327561595870967 126823638573491342393806451)
      ·
        refine ⟨190235457860237013590709677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126823638573491342393806451 190235457860237013590709677)
        ·
          refine ⟨71338296697588880096516129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190235457860237013590709677 71338296697588880096516129)
          ·
            refine ⟨53503722523191660072387097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71338296697588880096516129 53503722523191660072387097)
            ·
              refine ⟨40127791892393745054290323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53503722523191660072387097 40127791892393745054290323)
              ·
                refine ⟨60191687838590617581435485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40127791892393745054290323 60191687838590617581435485)
                ·
                  refine ⟨22571882939471481593038307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60191687838590617581435485 22571882939471481593038307)
                  ·
                    refine ⟨33857824409207222389557461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22571882939471481593038307 33857824409207222389557461)
                    ·
                      refine ⟨793542759590794274755253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 33857824409207222389557461 793542759590794274755253)
                      ·
                        rfl

theorem cell23_1545419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 7].length) (baseStart_1545419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1545419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1545419 prefixEnd_1545419 := by exact prefixLift 1545419
  have htrace : WordTrace (prefixWord ++ tailWord_1545419) baseStart_1545419 baseEnd_1545419 := by
    simpa [prefixWord, tailWord_1545419, baseEnd_1545419] using wordTrace_append hprefix tailTrace_1545419
  have hstable : (prefixWord ++ tailWord_1545419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545419).length < 2 ^ (prefixWord ++ tailWord_1545419).sum := by decide
  have hdescent : baseEnd_1545419 < baseStart_1545419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545426 : List Nat := [3, 2, 2, 2, 1, 1, 1, 3, 1, 7]
def baseStart_1545426 : Nat := 118140960795 + 1545426 * 2 ^ 59
def prefixEnd_1545426 : Nat := 4983230072969 + 3 ^ 40 * 1545426 * 2
def baseEnd_1545426 : Nat := 264515451318458582455907

theorem tailTrace_1545426 : CollatzResearch.WordTrace tailWord_1545426 prefixEnd_1545426 264515451318458582455907 := by
  unfold tailWord_1545426
  simp only [CollatzResearch.WordTrace]
  refine ⟨14091579224798253648188033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37577544599462009728501421 14091579224798253648188033)
  ·
    refine ⟨10568684418598690236141025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14091579224798253648188033 10568684418598690236141025)
    ·
      refine ⟨7926513313949017677105769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10568684418598690236141025 7926513313949017677105769)
      ·
        refine ⟨5944884985461763257829327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7926513313949017677105769 5944884985461763257829327)
        ·
          refine ⟨8917327478192644886743991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5944884985461763257829327 8917327478192644886743991)
          ·
            refine ⟨13375991217288967330115987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8917327478192644886743991 13375991217288967330115987)
            ·
              refine ⟨20063986825933450995173981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13375991217288967330115987 20063986825933450995173981)
              ·
                refine ⟨7523995059725044123190243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20063986825933450995173981 7523995059725044123190243)
                ·
                  refine ⟨11285992589587566184785365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7523995059725044123190243 11285992589587566184785365)
                  ·
                    refine ⟨264515451318458582455907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11285992589587566184785365 264515451318458582455907)
                    ·
                      rfl

theorem cell23_1545426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_1545426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1545426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1545426 prefixEnd_1545426 := by exact prefixLift 1545426
  have htrace : WordTrace (prefixWord ++ tailWord_1545426) baseStart_1545426 baseEnd_1545426 := by
    simpa [prefixWord, tailWord_1545426, baseEnd_1545426] using wordTrace_append hprefix tailTrace_1545426
  have hstable : (prefixWord ++ tailWord_1545426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545426).length < 2 ^ (prefixWord ++ tailWord_1545426).sum := by decide
  have hdescent : baseEnd_1545426 < baseStart_1545426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545447 : List Nat := [1, 1, 5, 3, 2, 1, 3, 2, 5]
def baseStart_1545447 : Nat := 118140960795 + 1545447 * 2 ^ 59
def prefixEnd_1545447 : Nat := 4983230072969 + 3 ^ 40 * 1545447 * 2
def baseEnd_1545447 : Nat := 88173015227680018356125

theorem tailTrace_1545447 : CollatzResearch.WordTrace tailWord_1545447 prefixEnd_1545447 88173015227680018356125 := by
  unfold tailWord_1545447
  simp only [CollatzResearch.WordTrace]
  refine ⟨56367082832116935179266595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37578055221411290119511063 56367082832116935179266595)
  ·
    refine ⟨84550624248175402768899893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56367082832116935179266595 84550624248175402768899893)
    ·
      refine ⟨7926621023266444009584365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84550624248175402768899893 7926621023266444009584365)
      ·
        refine ⟨2972482883724916503594137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7926621023266444009584365 2972482883724916503594137)
        ·
          refine ⟨2229362162793687377695603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2972482883724916503594137 2229362162793687377695603)
          ·
            refine ⟨3344043244190531066543405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2229362162793687377695603 3344043244190531066543405)
            ·
              refine ⟨1254016216571449149953777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3344043244190531066543405 1254016216571449149953777)
              ·
                refine ⟨940512162428586862465333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1254016216571449149953777 940512162428586862465333)
                ·
                  refine ⟨88173015227680018356125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 940512162428586862465333 88173015227680018356125)
                  ·
                    rfl

theorem cell23_1545447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3, 2, 5].length) (baseStart_1545447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1545447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1545447 prefixEnd_1545447 := by exact prefixLift 1545447
  have htrace : WordTrace (prefixWord ++ tailWord_1545447) baseStart_1545447 baseEnd_1545447 := by
    simpa [prefixWord, tailWord_1545447, baseEnd_1545447] using wordTrace_append hprefix tailTrace_1545447
  have hstable : (prefixWord ++ tailWord_1545447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545447).length < 2 ^ (prefixWord ++ tailWord_1545447).sum := by decide
  have hdescent : baseEnd_1545447 < baseStart_1545447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545453 : List Nat := [1, 5, 1, 2, 2, 2, 1, 1, 1, 2, 5]
def baseStart_1545453 : Nat := 118140960795 + 1545453 * 2 ^ 59
def prefixEnd_1545453 : Nat := 4983230072969 + 3 ^ 40 * 1545453 * 2
def baseEnd_1545453 : Nat := 793560217933047141730097

theorem tailTrace_1545453 : CollatzResearch.WordTrace tailWord_1545453 prefixEnd_1545453 793560217933047141730097 := by
  unfold tailWord_1545453
  simp only [CollatzResearch.WordTrace]
  refine ⟨56367301670095198203985013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37578201113396798802656675 56367301670095198203985013)
  ·
    refine ⟨5284434531571424831623595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56367301670095198203985013 5284434531571424831623595)
    ·
      refine ⟨7926651797357137247435393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5284434531571424831623595 7926651797357137247435393)
      ·
        refine ⟨5944988848017852935576545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7926651797357137247435393 5944988848017852935576545)
        ·
          refine ⟨4458741636013389701682409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5944988848017852935576545 4458741636013389701682409)
          ·
            refine ⟨3344056227010042276261807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4458741636013389701682409 3344056227010042276261807)
            ·
              refine ⟨5016084340515063414392711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3344056227010042276261807 5016084340515063414392711)
              ·
                refine ⟨7524126510772595121589067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5016084340515063414392711 7524126510772595121589067)
                ·
                  refine ⟨11286189766158892682383601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7524126510772595121589067 11286189766158892682383601)
                  ·
                    refine ⟨8464642324619169511787701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11286189766158892682383601 8464642324619169511787701)
                    ·
                      refine ⟨793560217933047141730097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8464642324619169511787701 793560217933047141730097)
                      ·
                        rfl

theorem cell23_1545453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_1545453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1545453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1545453 prefixEnd_1545453 := by exact prefixLift 1545453
  have htrace : WordTrace (prefixWord ++ tailWord_1545453) baseStart_1545453 baseEnd_1545453 := by
    simpa [prefixWord, tailWord_1545453, baseEnd_1545453] using wordTrace_append hprefix tailTrace_1545453
  have hstable : (prefixWord ++ tailWord_1545453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545453).length < 2 ^ (prefixWord ++ tailWord_1545453).sum := by decide
  have hdescent : baseEnd_1545453 < baseStart_1545453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545480 : List Nat := [2, 1, 3, 2, 4, 1, 2, 1, 2, 1, 4]
def baseStart_1545480 : Nat := 118140960795 + 1545480 * 2 ^ 59
def prefixEnd_1545480 : Nat := 4983230072969 + 3 ^ 40 * 1545480 * 2
def baseEnd_1545480 : Nat := 793574081910718536092473

theorem tailTrace_1545480 : CollatzResearch.WordTrace tailWord_1545480 prefixEnd_1545480 793574081910718536092473 := by
  unfold tailWord_1545480
  simp only [CollatzResearch.WordTrace]
  refine ⟨28184143220498690907608947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37578857627331587876811929 28184143220498690907608947)
  ·
    refine ⟨42276214830748036361413421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28184143220498690907608947 42276214830748036361413421)
    ·
      refine ⟨15853580561530513635530033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42276214830748036361413421 15853580561530513635530033)
      ·
        refine ⟨11890185421147885226647525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15853580561530513635530033 11890185421147885226647525)
        ·
          refine ⟨2229409766465228479996411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11890185421147885226647525 2229409766465228479996411)
          ·
            refine ⟨3344114649697842719994617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2229409766465228479996411 3344114649697842719994617)
            ·
              refine ⟨2508085987273382039995963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3344114649697842719994617 2508085987273382039995963)
              ·
                refine ⟨3762128980910073059993945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2508085987273382039995963 3762128980910073059993945)
                ·
                  refine ⟨2821596735682554794995459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3762128980910073059993945 2821596735682554794995459)
                  ·
                    refine ⟨4232395103523832192493189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2821596735682554794995459 4232395103523832192493189)
                    ·
                      refine ⟨793574081910718536092473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4232395103523832192493189 793574081910718536092473)
                      ·
                        rfl

theorem cell23_1545480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_1545480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1545480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1545480 prefixEnd_1545480 := by exact prefixLift 1545480
  have htrace : WordTrace (prefixWord ++ tailWord_1545480) baseStart_1545480 baseEnd_1545480 := by
    simpa [prefixWord, tailWord_1545480, baseEnd_1545480] using wordTrace_append hprefix tailTrace_1545480
  have hstable : (prefixWord ++ tailWord_1545480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545480).length < 2 ^ (prefixWord ++ tailWord_1545480).sum := by decide
  have hdescent : baseEnd_1545480 < baseStart_1545480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545483 : List Nat := [1, 1, 1, 1, 5, 3, 1, 3, 2, 2, 3]
def baseStart_1545483 : Nat := 118140960795 + 1545483 * 2 ^ 59
def prefixEnd_1545483 : Nat := 4983230072969 + 3 ^ 40 * 1545483 * 2
def baseEnd_1545483 : Nat := 793575622352682024354959

theorem tailTrace_1545483 : CollatzResearch.WordTrace tailWord_1545483 prefixEnd_1545483 793575622352682024354959 := by
  unfold tailWord_1545483
  simp only [CollatzResearch.WordTrace]
  refine ⟨56368395859986513327577103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37578930573324342218384735 56368395859986513327577103)
  ·
    refine ⟨84552593789979769991365655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56368395859986513327577103 84552593789979769991365655)
    ·
      refine ⟨126828890684969654987048483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84552593789979769991365655 126828890684969654987048483)
      ·
        refine ⟨190243336027454482480572725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126828890684969654987048483 190243336027454482480572725)
        ·
          refine ⟨17835312752573857732553693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 190243336027454482480572725 17835312752573857732553693)
          ·
            refine ⟨6688242282215196649707635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17835312752573857732553693 6688242282215196649707635)
            ·
              refine ⟨10032363423322794974561453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6688242282215196649707635 10032363423322794974561453)
              ·
                refine ⟨3762136283746048115460545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10032363423322794974561453 3762136283746048115460545)
                ·
                  refine ⟨2821602212809536086595409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3762136283746048115460545 2821602212809536086595409)
                  ·
                    refine ⟨2116201659607152064946557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2821602212809536086595409 2116201659607152064946557)
                    ·
                      refine ⟨793575622352682024354959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2116201659607152064946557 793575622352682024354959)
                      ·
                        rfl

theorem cell23_1545483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 3, 2, 2, 3].length) (baseStart_1545483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1545483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1545483 prefixEnd_1545483 := by exact prefixLift 1545483
  have htrace : WordTrace (prefixWord ++ tailWord_1545483) baseStart_1545483 baseEnd_1545483 := by
    simpa [prefixWord, tailWord_1545483, baseEnd_1545483] using wordTrace_append hprefix tailTrace_1545483
  have hstable : (prefixWord ++ tailWord_1545483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545483).length < 2 ^ (prefixWord ++ tailWord_1545483).sum := by decide
  have hdescent : baseEnd_1545483 < baseStart_1545483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545507 : List Nat := [1, 1, 1, 4, 2, 3, 4, 2, 1, 4]
def baseStart_1545507 : Nat := 118140960795 + 1545507 * 2 ^ 59
def prefixEnd_1545507 : Nat := 4983230072969 + 3 ^ 40 * 1545507 * 2
def baseEnd_1545507 : Nat := 264529315296129976818283

theorem tailTrace_1545507 : CollatzResearch.WordTrace tailWord_1545507 prefixEnd_1545507 264529315296129976818283 := by
  unfold tailWord_1545507
  simp only [CollatzResearch.WordTrace]
  refine ⟨56369271211899565426450775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37579514141266376950967183 56369271211899565426450775)
  ·
    refine ⟨84553906817849348139676163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56369271211899565426450775 84553906817849348139676163)
    ·
      refine ⟨126830860226774022209514245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84553906817849348139676163 126830860226774022209514245)
      ·
        refine ⟨23780786292520129164283921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126830860226774022209514245 23780786292520129164283921)
        ·
          refine ⟨17835589719390096873212941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23780786292520129164283921 17835589719390096873212941)
          ·
            refine ⟨6688346144771286327454853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17835589719390096873212941 6688346144771286327454853)
            ·
              refine ⟨1254064902144616186397785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6688346144771286327454853 1254064902144616186397785)
              ·
                refine ⟨940548676608462139798339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1254064902144616186397785 940548676608462139798339)
                ·
                  refine ⟨1410823014912693209697509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 940548676608462139798339 1410823014912693209697509)
                  ·
                    refine ⟨264529315296129976818283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1410823014912693209697509 264529315296129976818283)
                    ·
                      rfl

theorem cell23_1545507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4, 2, 1, 4].length) (baseStart_1545507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1545507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1545507 prefixEnd_1545507 := by exact prefixLift 1545507
  have htrace : WordTrace (prefixWord ++ tailWord_1545507) baseStart_1545507 baseEnd_1545507 := by
    simpa [prefixWord, tailWord_1545507, baseEnd_1545507] using wordTrace_append hprefix tailTrace_1545507
  have hstable : (prefixWord ++ tailWord_1545507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545507).length < 2 ^ (prefixWord ++ tailWord_1545507).sum := by decide
  have hdescent : baseEnd_1545507 < baseStart_1545507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545530 : List Nat := [3, 1, 1, 1, 4, 1, 3, 2, 3, 1, 3]
def baseStart_1545530 : Nat := 118140960795 + 1545530 * 2 ^ 59
def prefixEnd_1545530 : Nat := 4983230072969 + 3 ^ 40 * 1545530 * 2
def baseEnd_1545530 : Nat := 793599755943443340467243

theorem tailTrace_1545530 : CollatzResearch.WordTrace tailWord_1545530 prefixEnd_1545530 793599755943443340467243 := by
  unfold tailWord_1545530
  simp only [CollatzResearch.WordTrace]
  refine ⟨14092527522704060088634511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37580073393877493569692029 14092527522704060088634511)
  ·
    refine ⟨21138791284056090132951767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14092527522704060088634511 21138791284056090132951767)
    ·
      refine ⟨31708186926084135199427651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21138791284056090132951767 31708186926084135199427651)
      ·
        refine ⟨47562280389126202799141477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31708186926084135199427651 47562280389126202799141477)
        ·
          refine ⟨8917927572961163024839027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47562280389126202799141477 8917927572961163024839027)
          ·
            refine ⟨13376891359441744537258541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8917927572961163024839027 13376891359441744537258541)
            ·
              refine ⟨5016334259790654201471953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13376891359441744537258541 5016334259790654201471953)
              ·
                refine ⟨3762250694842990651103965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5016334259790654201471953 3762250694842990651103965)
                ·
                  refine ⟨1410844010566121494163987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3762250694842990651103965 1410844010566121494163987)
                  ·
                    refine ⟨2116266015849182241245981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1410844010566121494163987 2116266015849182241245981)
                    ·
                      refine ⟨793599755943443340467243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2116266015849182241245981 793599755943443340467243)
                      ·
                        rfl

theorem cell23_1545530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 2, 3, 1, 3].length) (baseStart_1545530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1545530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1545530 prefixEnd_1545530 := by exact prefixLift 1545530
  have htrace : WordTrace (prefixWord ++ tailWord_1545530) baseStart_1545530 baseEnd_1545530 := by
    simpa [prefixWord, tailWord_1545530, baseEnd_1545530] using wordTrace_append hprefix tailTrace_1545530
  have hstable : (prefixWord ++ tailWord_1545530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545530).length < 2 ^ (prefixWord ++ tailWord_1545530).sum := by decide
  have hdescent : baseEnd_1545530 < baseStart_1545530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545573 : List Nat := [1, 3, 1, 3, 1, 2, 3, 2, 1, 1, 5]
def baseStart_1545573 : Nat := 118140960795 + 1545573 * 2 ^ 59
def prefixEnd_1545573 : Nat := 4983230072969 + 3 ^ 40 * 1545573 * 2
def baseEnd_1545573 : Nat := 793621835611586672229545

theorem tailTrace_1545573 : CollatzResearch.WordTrace tailWord_1545573 prefixEnd_1545573 793621835611586672229545 := by
  unfold tailWord_1545573
  simp only [CollatzResearch.WordTrace]
  refine ⟨56371678429660458698353373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37581118953106972465568915 56371678429660458698353373)
  ·
    refine ⟨21139379411122672011882515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56371678429660458698353373 21139379411122672011882515)
    ·
      refine ⟨31709069116684008017823773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21139379411122672011882515 31709069116684008017823773)
      ·
        refine ⟨11890900918756503006683915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31709069116684008017823773 11890900918756503006683915)
        ·
          refine ⟨17836351378134754510025873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11890900918756503006683915 17836351378134754510025873)
          ·
            refine ⟨13377263533601065882519405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17836351378134754510025873 13377263533601065882519405)
            ·
              refine ⟨5016473825100399705944777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13377263533601065882519405 5016473825100399705944777)
              ·
                refine ⟨3762355368825299779458583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5016473825100399705944777 3762355368825299779458583)
                ·
                  refine ⟨5643533053237949669187875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3762355368825299779458583 5643533053237949669187875)
                  ·
                    refine ⟨8465299579856924503781813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5643533053237949669187875 8465299579856924503781813)
                    ·
                      refine ⟨793621835611586672229545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8465299579856924503781813 793621835611586672229545)
                      ·
                        rfl

theorem cell23_1545573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_1545573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1545573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1545573 prefixEnd_1545573 := by exact prefixLift 1545573
  have htrace : WordTrace (prefixWord ++ tailWord_1545573) baseStart_1545573 baseEnd_1545573 := by
    simpa [prefixWord, tailWord_1545573, baseEnd_1545573] using wordTrace_append hprefix tailTrace_1545573
  have hstable : (prefixWord ++ tailWord_1545573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545573).length < 2 ^ (prefixWord ++ tailWord_1545573).sum := by decide
  have hdescent : baseEnd_1545573 < baseStart_1545573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545580 : List Nat := [2, 2, 1, 1, 5, 3, 1, 1, 1, 6]
def baseStart_1545580 : Nat := 118140960795 + 1545580 * 2 ^ 59
def prefixEnd_1545580 : Nat := 4983230072969 + 3 ^ 40 * 1545580 * 2
def baseEnd_1545580 : Nat := 264541809992056048280671

theorem tailTrace_1545580 : CollatzResearch.WordTrace tailWord_1545580 prefixEnd_1545580 264541809992056048280671 := by
  unfold tailWord_1545580
  simp only [CollatzResearch.WordTrace]
  refine ⟨28185966870317549446929097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37581289160423399262572129 28185966870317549446929097)
  ·
    refine ⟨21139475152738162085196823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28185966870317549446929097 21139475152738162085196823)
    ·
      refine ⟨31709212729107243127795235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21139475152738162085196823 31709212729107243127795235)
      ·
        refine ⟨47563819093660864691692853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31709212729107243127795235 47563819093660864691692853)
        ·
          refine ⟨4459108040030706064846205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47563819093660864691692853 4459108040030706064846205)
          ·
            refine ⟨1672165515011514774317327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4459108040030706064846205 1672165515011514774317327)
            ·
              refine ⟨2508248272517272161475991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1672165515011514774317327 2508248272517272161475991)
              ·
                refine ⟨3762372408775908242213987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2508248272517272161475991 3762372408775908242213987)
                ·
                  refine ⟨5643558613163862363320981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3762372408775908242213987 5643558613163862363320981)
                  ·
                    refine ⟨264541809992056048280671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5643558613163862363320981 264541809992056048280671)
                    ·
                      rfl

theorem cell23_1545580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 6].length) (baseStart_1545580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1545580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1545580 prefixEnd_1545580 := by exact prefixLift 1545580
  have htrace : WordTrace (prefixWord ++ tailWord_1545580) baseStart_1545580 baseEnd_1545580 := by
    simpa [prefixWord, tailWord_1545580, baseEnd_1545580] using wordTrace_append hprefix tailTrace_1545580
  have hstable : (prefixWord ++ tailWord_1545580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545580).length < 2 ^ (prefixWord ++ tailWord_1545580).sum := by decide
  have hdescent : baseEnd_1545580 < baseStart_1545580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545593 : List Nat := [1, 2, 1, 3, 2, 1, 6, 7]
def baseStart_1545593 : Nat := 118140960795 + 1545593 * 2 ^ 59
def prefixEnd_1545593 : Nat := 4983230072969 + 3 ^ 40 * 1545593 * 2
def baseEnd_1545593 : Nat := 29393781674988021999239

theorem tailTrace_1545593 : CollatzResearch.WordTrace tailWord_1545593 prefixEnd_1545593 29393781674988021999239 := by
  unfold tailWord_1545593
  simp only [CollatzResearch.WordTrace]
  refine ⟨56372407889588002114081433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37581605259725334742720955 56372407889588002114081433)
  ·
    refine ⟨42279305917191001585561075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56372407889588002114081433 42279305917191001585561075)
    ·
      refine ⟨63418958875786502378341613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42279305917191001585561075 63418958875786502378341613)
      ·
        refine ⟨23782109578419938391878105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63418958875786502378341613 23782109578419938391878105)
        ·
          refine ⟨17836582183814953793908579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23782109578419938391878105 17836582183814953793908579)
          ·
            refine ⟨26754873275722430690862869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17836582183814953793908579 26754873275722430690862869)
            ·
              refine ⟨1254134684799488938634197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 26754873275722430690862869 1254134684799488938634197)
              ·
                refine ⟨29393781674988021999239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1254134684799488938634197 29393781674988021999239)
                ·
                  rfl

theorem cell23_1545593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6, 7].length) (baseStart_1545593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1545593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1545593 prefixEnd_1545593 := by exact prefixLift 1545593
  have htrace : WordTrace (prefixWord ++ tailWord_1545593) baseStart_1545593 baseEnd_1545593 := by
    simpa [prefixWord, tailWord_1545593, baseEnd_1545593] using wordTrace_append hprefix tailTrace_1545593
  have hstable : (prefixWord ++ tailWord_1545593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545593).length < 2 ^ (prefixWord ++ tailWord_1545593).sum := by decide
  have hdescent : baseEnd_1545593 < baseStart_1545593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545616 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 7]
def baseStart_1545616 : Nat := 118140960795 + 1545616 * 2 ^ 59
def prefixEnd_1545616 : Nat := 4983230072969 + 3 ^ 40 * 1545616 * 2
def baseEnd_1545616 : Nat := 793643915279730003991847

theorem tailTrace_1545616 : CollatzResearch.WordTrace tailWord_1545616 prefixEnd_1545616 793643915279730003991847 := by
  unfold tailWord_1545616
  simp only [CollatzResearch.WordTrace]
  refine ⟨28186623384252338521084351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37582164512336451361445801 28186623384252338521084351)
  ·
    refine ⟨42279935076378507781626527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28186623384252338521084351 42279935076378507781626527)
    ·
      refine ⟨63419902614567761672439791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42279935076378507781626527 63419902614567761672439791)
      ·
        refine ⟨95129853921851642508659687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63419902614567761672439791 95129853921851642508659687)
        ·
          refine ⟨142694780882777463762989531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95129853921851642508659687 142694780882777463762989531)
          ·
            refine ⟨214042171324166195644484297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142694780882777463762989531 214042171324166195644484297)
            ·
              refine ⟨160531628493124646733363223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 214042171324166195644484297 160531628493124646733363223)
              ·
                refine ⟨240797442739686970100044835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160531628493124646733363223 240797442739686970100044835)
                ·
                  refine ⟨361196164109530455150067253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 240797442739686970100044835 361196164109530455150067253)
                  ·
                    refine ⟨33862140385268480170318805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 361196164109530455150067253 33862140385268480170318805)
                    ·
                      refine ⟨793643915279730003991847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 33862140385268480170318805 793643915279730003991847)
                      ·
                        rfl

theorem cell23_1545616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 7].length) (baseStart_1545616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1545616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1545616 prefixEnd_1545616 := by exact prefixLift 1545616
  have htrace : WordTrace (prefixWord ++ tailWord_1545616) baseStart_1545616 baseEnd_1545616 := by
    simpa [prefixWord, tailWord_1545616, baseEnd_1545616] using wordTrace_append hprefix tailTrace_1545616
  have hstable : (prefixWord ++ tailWord_1545616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545616).length < 2 ^ (prefixWord ++ tailWord_1545616).sum := by decide
  have hdescent : baseEnd_1545616 < baseStart_1545616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545663 : List Nat := [1, 1, 2, 2, 2, 1, 1, 2, 4, 4, 3]
def baseStart_1545663 : Nat := 118140960795 + 1545663 * 2 ^ 59
def prefixEnd_1545663 : Nat := 4983230072969 + 3 ^ 40 * 1545663 * 2
def baseEnd_1545663 : Nat := 793668048870491320104131

theorem tailTrace_1545663 : CollatzResearch.WordTrace tailWord_1545663 prefixEnd_1545663 793668048870491320104131 := by
  unfold tailWord_1545663
  simp only [CollatzResearch.WordTrace]
  refine ⟨56374960999334404069129643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37583307332889602712753095 56374960999334404069129643)
  ·
    refine ⟨84562441499001606103694465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56374960999334404069129643 84562441499001606103694465)
    ·
      refine ⟨63421831124251204577770849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84562441499001606103694465 63421831124251204577770849)
      ·
        refine ⟨47566373343188403433328137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63421831124251204577770849 47566373343188403433328137)
        ·
          refine ⟨35674780007391302574996103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47566373343188403433328137 35674780007391302574996103)
          ·
            refine ⟨53512170011086953862494155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35674780007391302574996103 53512170011086953862494155)
            ·
              refine ⟨80268255016630430793741233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53512170011086953862494155 80268255016630430793741233)
              ·
                refine ⟨60201191262472823095305925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80268255016630430793741233 60201191262472823095305925)
                ·
                  refine ⟨11287723361713654330369861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60201191262472823095305925 11287723361713654330369861)
                  ·
                    refine ⟨2116448130321310186944349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11287723361713654330369861 2116448130321310186944349)
                    ·
                      refine ⟨793668048870491320104131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2116448130321310186944349 793668048870491320104131)
                      ·
                        rfl

theorem cell23_1545663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 4, 3].length) (baseStart_1545663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1545663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1545663 prefixEnd_1545663 := by exact prefixLift 1545663
  have htrace : WordTrace (prefixWord ++ tailWord_1545663) baseStart_1545663 baseEnd_1545663 := by
    simpa [prefixWord, tailWord_1545663, baseEnd_1545663] using wordTrace_append hprefix tailTrace_1545663
  have hstable : (prefixWord ++ tailWord_1545663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545663).length < 2 ^ (prefixWord ++ tailWord_1545663).sum := by decide
  have hdescent : baseEnd_1545663 < baseStart_1545663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545673 : List Nat := [1, 2, 1, 1, 2, 1, 3, 4, 2, 2, 4]
def baseStart_1545673 : Nat := 118140960795 + 1545673 * 2 ^ 59
def prefixEnd_1545673 : Nat := 4983230072969 + 3 ^ 40 * 1545673 * 2
def baseEnd_1545673 : Nat := 793673183677036280979085

theorem tailTrace_1545673 : CollatzResearch.WordTrace tailWord_1545673 prefixEnd_1545673 793673183677036280979085 := by
  unfold tailWord_1545673
  simp only [CollatzResearch.WordTrace]
  refine ⟨56375325729298175776993673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37583550486198783851329115 56375325729298175776993673)
  ·
    refine ⟨42281494296973631832745255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56375325729298175776993673 42281494296973631832745255)
    ·
      refine ⟨63422241445460447749117883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42281494296973631832745255 63422241445460447749117883)
      ·
        refine ⟨95133362168190671623676825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63422241445460447749117883 95133362168190671623676825)
        ·
          refine ⟨71350021626143003717757619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95133362168190671623676825 71350021626143003717757619)
          ·
            refine ⟨107025032439214505576636429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71350021626143003717757619 107025032439214505576636429)
            ·
              refine ⟨40134387164705439591238661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107025032439214505576636429 40134387164705439591238661)
              ·
                refine ⟨7525197593382269923357249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40134387164705439591238661 7525197593382269923357249)
                ·
                  refine ⟨5643898195036702442517937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7525197593382269923357249 5643898195036702442517937)
                  ·
                    refine ⟨4232923646277526831888453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5643898195036702442517937 4232923646277526831888453)
                    ·
                      refine ⟨793673183677036280979085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4232923646277526831888453 793673183677036280979085)
                      ·
                        rfl

theorem cell23_1545673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 2, 2, 4].length) (baseStart_1545673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1545673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1545673 prefixEnd_1545673 := by exact prefixLift 1545673
  have htrace : WordTrace (prefixWord ++ tailWord_1545673) baseStart_1545673 baseEnd_1545673 := by
    simpa [prefixWord, tailWord_1545673, baseEnd_1545673] using wordTrace_append hprefix tailTrace_1545673
  have hstable : (prefixWord ++ tailWord_1545673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545673).length < 2 ^ (prefixWord ++ tailWord_1545673).sum := by decide
  have hdescent : baseEnd_1545673 < baseStart_1545673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545690 : List Nat := [3, 1, 1, 2, 3, 3, 1, 1, 2, 2, 4]
def baseStart_1545690 : Nat := 118140960795 + 1545690 * 2 ^ 59
def prefixEnd_1545690 : Nat := 4983230072969 + 3 ^ 40 * 1545690 * 2
def baseEnd_1545690 : Nat := 793681912848162714466507

theorem tailTrace_1545690 : CollatzResearch.WordTrace tailWord_1545690 prefixEnd_1545690 793681912848162714466507 := by
  unfold tailWord_1545690
  simp only [CollatzResearch.WordTrace]
  refine ⟨14093986442559146920090631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37583963846824391786908349 14093986442559146920090631)
  ·
    refine ⟨21140979663838720380135947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14093986442559146920090631 21140979663838720380135947)
    ·
      refine ⟨31711469495758080570203921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21140979663838720380135947 31711469495758080570203921)
      ·
        refine ⟨23783602121818560427652941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31711469495758080570203921 23783602121818560427652941)
        ·
          refine ⟨8918850795681960160369853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23783602121818560427652941 8918850795681960160369853)
          ·
            refine ⟨3344569048380735060138695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8918850795681960160369853 3344569048380735060138695)
            ·
              refine ⟨5016853572571102590208043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3344569048380735060138695 5016853572571102590208043)
              ·
                refine ⟨7525280358856653885312065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5016853572571102590208043 7525280358856653885312065)
                ·
                  refine ⟨5643960269142490413984049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7525280358856653885312065 5643960269142490413984049)
                  ·
                    refine ⟨4232970201856867810488037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5643960269142490413984049 4232970201856867810488037)
                    ·
                      refine ⟨793681912848162714466507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4232970201856867810488037 793681912848162714466507)
                      ·
                        rfl

theorem cell23_1545690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 2, 2, 4].length) (baseStart_1545690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1545690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1545690 prefixEnd_1545690 := by exact prefixLift 1545690
  have htrace : WordTrace (prefixWord ++ tailWord_1545690) baseStart_1545690 baseEnd_1545690 := by
    simpa [prefixWord, tailWord_1545690, baseEnd_1545690] using wordTrace_append hprefix tailTrace_1545690
  have hstable : (prefixWord ++ tailWord_1545690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545690).length < 2 ^ (prefixWord ++ tailWord_1545690).sum := by decide
  have hdescent : baseEnd_1545690 < baseStart_1545690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545710 : List Nat := [4, 1, 2, 1, 2, 1, 1, 2, 1, 5, 3]
def baseStart_1545710 : Nat := 118140960795 + 1545710 * 2 ^ 59
def prefixEnd_1545710 : Nat := 4983230072969 + 3 ^ 40 * 1545710 * 2
def baseEnd_1545710 : Nat := 793692182461252636216415

theorem tailTrace_1545710 : CollatzResearch.WordTrace tailWord_1545710 prefixEnd_1545710 793692182461252636216415 := by
  unfold tailWord_1545710
  simp only [CollatzResearch.WordTrace]
  refine ⟨7047084403770516387011323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37584450153442754064060389 7047084403770516387011323)
  ·
    refine ⟨10570626605655774580516985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7047084403770516387011323 10570626605655774580516985)
    ·
      refine ⟨7927969954241830935387739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10570626605655774580516985 7927969954241830935387739)
      ·
        refine ⟨11891954931362746403081609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7927969954241830935387739 11891954931362746403081609)
        ·
          refine ⟨8918966198522059802311207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11891954931362746403081609 8918966198522059802311207)
          ·
            refine ⟨13378449297783089703466811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8918966198522059802311207 13378449297783089703466811)
            ·
              refine ⟨20067673946674634555200217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13378449297783089703466811 20067673946674634555200217)
              ·
                refine ⟨15050755460005975916400163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20067673946674634555200217 15050755460005975916400163)
                ·
                  refine ⟨22576133190008963874600245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15050755460005975916400163 22576133190008963874600245)
                  ·
                    refine ⟨2116512486563340363243773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22576133190008963874600245 2116512486563340363243773)
                    ·
                      refine ⟨793692182461252636216415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2116512486563340363243773 793692182461252636216415)
                      ·
                        rfl

theorem cell23_1545710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_1545710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1545710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1545710 prefixEnd_1545710 := by exact prefixLift 1545710
  have htrace : WordTrace (prefixWord ++ tailWord_1545710) baseStart_1545710 baseEnd_1545710 := by
    simpa [prefixWord, tailWord_1545710, baseEnd_1545710] using wordTrace_append hprefix tailTrace_1545710
  have hstable : (prefixWord ++ tailWord_1545710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545710).length < 2 ^ (prefixWord ++ tailWord_1545710).sum := by decide
  have hdescent : baseEnd_1545710 < baseStart_1545710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545803 : List Nat := [1, 1, 1, 1, 3, 1, 3, 1, 2, 9]
def baseStart_1545803 : Nat := 118140960795 + 1545803 * 2 ^ 59
def prefixEnd_1545803 : Nat := 4983230072969 + 3 ^ 40 * 1545803 * 2
def baseEnd_1545803 : Nat := 264579978720706924117829

theorem tailTrace_1545803 : CollatzResearch.WordTrace tailWord_1545803 prefixEnd_1545803 264579978720706924117829 := by
  unfold tailWord_1545803
  simp only [CollatzResearch.WordTrace]
  refine ⟨56380067218827207979226063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37586711479218138652817375 56380067218827207979226063)
  ·
    refine ⟨84570100828240811968839095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56380067218827207979226063 84570100828240811968839095)
    ·
      refine ⟨126855151242361217953258643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84570100828240811968839095 126855151242361217953258643)
      ·
        refine ⟨190282726863541826929887965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126855151242361217953258643 190282726863541826929887965)
        ·
          refine ⟨71356022573828185098707987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190282726863541826929887965 71356022573828185098707987)
          ·
            refine ⟨107034033860742277648061981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71356022573828185098707987 107034033860742277648061981)
            ·
              refine ⟨40137762697778354118023243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107034033860742277648061981 40137762697778354118023243)
              ·
                refine ⟨60206644046667531177034865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40137762697778354118023243 60206644046667531177034865)
                ·
                  refine ⟨45154983035000648382776149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60206644046667531177034865 45154983035000648382776149)
                  ·
                    refine ⟨264579978720706924117829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 45154983035000648382776149 264579978720706924117829)
                    ·
                      rfl

theorem cell23_1545803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 9].length) (baseStart_1545803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1545803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1545803 prefixEnd_1545803 := by exact prefixLift 1545803
  have htrace : WordTrace (prefixWord ++ tailWord_1545803) baseStart_1545803 baseEnd_1545803 := by
    simpa [prefixWord, tailWord_1545803, baseEnd_1545803] using wordTrace_append hprefix tailTrace_1545803
  have hstable : (prefixWord ++ tailWord_1545803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545803).length < 2 ^ (prefixWord ++ tailWord_1545803).sum := by decide
  have hdescent : baseEnd_1545803 < baseStart_1545803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545817 : List Nat := [1, 2, 1, 2, 2, 1, 1, 6, 3, 1, 3]
def baseStart_1545817 : Nat := 118140960795 + 1545817 * 2 ^ 59
def prefixEnd_1545817 : Nat := 4983230072969 + 3 ^ 40 * 1545817 * 2
def baseEnd_1545817 : Nat := 793747124891283717578423

theorem tailTrace_1545817 : CollatzResearch.WordTrace tailWord_1545817 prefixEnd_1545817 793747124891283717578423 := by
  unfold tailWord_1545817
  simp only [CollatzResearch.WordTrace]
  refine ⟨56380577840776488370235705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37587051893850992246823803 56380577840776488370235705)
  ·
    refine ⟨42285433380582366277676779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56380577840776488370235705 42285433380582366277676779)
    ·
      refine ⟨63428150070873549416515169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42285433380582366277676779 63428150070873549416515169)
      ·
        refine ⟨47571112553155162062386377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63428150070873549416515169 47571112553155162062386377)
        ·
          refine ⟨35678334414866371546789783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47571112553155162062386377 35678334414866371546789783)
          ·
            refine ⟨53517501622299557320184675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35678334414866371546789783 53517501622299557320184675)
            ·
              refine ⟨80276252433449335980277013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53517501622299557320184675 80276252433449335980277013)
              ·
                refine ⟨3762949332817937624075485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 80276252433449335980277013 3762949332817937624075485)
                ·
                  refine ⟨1411105999806726609028307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3762949332817937624075485 1411105999806726609028307)
                  ·
                    refine ⟨2116658999710089913542461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1411105999806726609028307 2116658999710089913542461)
                    ·
                      refine ⟨793747124891283717578423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2116658999710089913542461 793747124891283717578423)
                      ·
                        rfl

theorem cell23_1545817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6, 3, 1, 3].length) (baseStart_1545817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1545817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1545817 prefixEnd_1545817 := by exact prefixLift 1545817
  have htrace : WordTrace (prefixWord ++ tailWord_1545817) baseStart_1545817 baseEnd_1545817 := by
    simpa [prefixWord, tailWord_1545817, baseEnd_1545817] using wordTrace_append hprefix tailTrace_1545817
  have hstable : (prefixWord ++ tailWord_1545817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545817).length < 2 ^ (prefixWord ++ tailWord_1545817).sum := by decide
  have hdescent : baseEnd_1545817 < baseStart_1545817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545857 : List Nat := [1, 2, 4, 2, 1, 2, 1, 2, 3, 1, 4]
def baseStart_1545857 : Nat := 118140960795 + 1545857 * 2 ^ 59
def prefixEnd_1545857 : Nat := 4983230072969 + 3 ^ 40 * 1545857 * 2
def baseEnd_1545857 : Nat := 793767664117463561078239

theorem tailTrace_1545857 : CollatzResearch.WordTrace tailWord_1545857 prefixEnd_1545857 793767664117463561078239 := by
  unfold tailWord_1545857
  simp only [CollatzResearch.WordTrace]
  refine ⟨56382036760631575201691825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37588024507087716801127883 56382036760631575201691825)
  ·
    refine ⟨42286527570473681401268869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56382036760631575201691825 42286527570473681401268869)
    ·
      refine ⟨7928723919463815262737913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42286527570473681401268869 7928723919463815262737913)
      ·
        refine ⟨5946542939597861447053435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7928723919463815262737913 5946542939597861447053435)
        ·
          refine ⟨8919814409396792170580153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5946542939597861447053435 8919814409396792170580153)
          ·
            refine ⟨6689860807047594127935115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8919814409396792170580153 6689860807047594127935115)
            ·
              refine ⟨10034791210571391191902673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6689860807047594127935115 10034791210571391191902673)
              ·
                refine ⟨7526093407928543393927005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10034791210571391191902673 7526093407928543393927005)
                ·
                  refine ⟨2822285027973203772722627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7526093407928543393927005 2822285027973203772722627)
                  ·
                    refine ⟨4233427541959805659083941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2822285027973203772722627 4233427541959805659083941)
                    ·
                      refine ⟨793767664117463561078239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4233427541959805659083941 793767664117463561078239)
                      ·
                        rfl

theorem cell23_1545857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_1545857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1545857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1545857 prefixEnd_1545857 := by exact prefixLift 1545857
  have htrace : WordTrace (prefixWord ++ tailWord_1545857) baseStart_1545857 baseEnd_1545857 := by
    simpa [prefixWord, tailWord_1545857, baseEnd_1545857] using wordTrace_append hprefix tailTrace_1545857
  have hstable : (prefixWord ++ tailWord_1545857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545857).length < 2 ^ (prefixWord ++ tailWord_1545857).sum := by decide
  have hdescent : baseEnd_1545857 < baseStart_1545857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545867 : List Nat := [1, 1, 1, 1, 4, 1, 3, 5, 2, 4]
def baseStart_1545867 : Nat := 118140960795 + 1545867 * 2 ^ 59
def prefixEnd_1545867 : Nat := 4983230072969 + 3 ^ 40 * 1545867 * 2
def baseEnd_1545867 : Nat := 264590932974669507317731

theorem tailTrace_1545867 : CollatzResearch.WordTrace tailWord_1545867 prefixEnd_1545867 264590932974669507317731 := by
  unfold tailWord_1545867
  simp only [CollatzResearch.WordTrace]
  refine ⟨56382401490595346909555855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37588267660396897939703903 56382401490595346909555855)
  ·
    refine ⟨84573602235893020364333783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56382401490595346909555855 84573602235893020364333783)
    ·
      refine ⟨126860403353839530546500675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84573602235893020364333783 126860403353839530546500675)
      ·
        refine ⟨190290605030759295819751013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126860403353839530546500675 190290605030759295819751013)
        ·
          refine ⟨35679488443267367966203315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 190290605030759295819751013 35679488443267367966203315)
          ·
            refine ⟨53519232664901051949304973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35679488443267367966203315 53519232664901051949304973)
            ·
              refine ⟨20069712249337894480989365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53519232664901051949304973 20069712249337894480989365)
              ·
                refine ⟨1881535523375427607592753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20069712249337894480989365 1881535523375427607592753)
                ·
                  refine ⟨1411151642531570705694565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1881535523375427607592753 1411151642531570705694565)
                  ·
                    refine ⟨264590932974669507317731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1411151642531570705694565 264590932974669507317731)
                    ·
                      rfl

theorem cell23_1545867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 5, 2, 4].length) (baseStart_1545867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1545867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1545867 prefixEnd_1545867 := by exact prefixLift 1545867
  have htrace : WordTrace (prefixWord ++ tailWord_1545867) baseStart_1545867 baseEnd_1545867 := by
    simpa [prefixWord, tailWord_1545867, baseEnd_1545867] using wordTrace_append hprefix tailTrace_1545867
  have hstable : (prefixWord ++ tailWord_1545867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545867).length < 2 ^ (prefixWord ++ tailWord_1545867).sum := by decide
  have hdescent : baseEnd_1545867 < baseStart_1545867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545967 : List Nat := [1, 1, 2, 1, 5, 1, 2, 1, 2, 4, 3]
def baseStart_1545967 : Nat := 118140960795 + 1545967 * 2 ^ 59
def prefixEnd_1545967 : Nat := 4983230072969 + 3 ^ 40 * 1545967 * 2
def baseEnd_1545967 : Nat := 793824146989458130702733

theorem tailTrace_1545967 : CollatzResearch.WordTrace tailWord_1545967 prefixEnd_1545967 793824146989458130702733 := by
  unfold tailWord_1545967
  simp only [CollatzResearch.WordTrace]
  refine ⟨56386048790233063988196155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37590699193488709325464103 56386048790233063988196155)
  ·
    refine ⟨84579073185349595982294233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56386048790233063988196155 84579073185349595982294233)
    ·
      refine ⟨63434304889012196986720675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84579073185349595982294233 63434304889012196986720675)
      ·
        refine ⟨95151457333518295480081013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63434304889012196986720675 95151457333518295480081013)
        ·
          refine ⟨8920449125017340201257595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 95151457333518295480081013 8920449125017340201257595)
          ·
            refine ⟨13380673687526010301886393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8920449125017340201257595 13380673687526010301886393)
            ·
              refine ⟨10035505265644507726414795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13380673687526010301886393 10035505265644507726414795)
              ·
                refine ⟨15053257898466761589622193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10035505265644507726414795 15053257898466761589622193)
                ·
                  refine ⟨11289943423850071192216645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15053257898466761589622193 11289943423850071192216645)
                  ·
                    refine ⟨2116864391971888348540621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11289943423850071192216645 2116864391971888348540621)
                    ·
                      refine ⟨793824146989458130702733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2116864391971888348540621 793824146989458130702733)
                      ·
                        rfl

theorem cell23_1545967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 4, 3].length) (baseStart_1545967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1545967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1545967 prefixEnd_1545967 := by exact prefixLift 1545967
  have htrace : WordTrace (prefixWord ++ tailWord_1545967) baseStart_1545967 baseEnd_1545967 := by
    simpa [prefixWord, tailWord_1545967, baseEnd_1545967] using wordTrace_append hprefix tailTrace_1545967
  have hstable : (prefixWord ++ tailWord_1545967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545967).length < 2 ^ (prefixWord ++ tailWord_1545967).sum := by decide
  have hdescent : baseEnd_1545967 < baseStart_1545967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546021 : List Nat := [1, 3, 1, 2, 3, 2, 4, 2, 5]
def baseStart_1546021 : Nat := 118140960795 + 1546021 * 2 ^ 59
def prefixEnd_1546021 : Nat := 4983230072969 + 3 ^ 40 * 1546021 * 2
def baseEnd_1546021 : Nat := 88205763882755657714165

theorem tailTrace_1546021 : CollatzResearch.WordTrace tailWord_1546021 prefixEnd_1546021 88205763882755657714165 := by
  unfold tailWord_1546021
  simp only [CollatzResearch.WordTrace]
  refine ⟨56388018332037431210661917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37592012221358287473774611 56388018332037431210661917)
  ·
    refine ⟨21145506874514036703998219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56388018332037431210661917 21145506874514036703998219)
    ·
      refine ⟨31718260311771055055997329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21145506874514036703998219 31718260311771055055997329)
      ·
        refine ⟨23788695233828291291997997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31718260311771055055997329 23788695233828291291997997)
        ·
          refine ⟨8920760712685609234499249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23788695233828291291997997 8920760712685609234499249)
          ·
            refine ⟨6690570534514206925874437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8920760712685609234499249 6690570534514206925874437)
            ·
              refine ⟨1254481975221413798601457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6690570534514206925874437 1254481975221413798601457)
              ·
                refine ⟨940861481416060348951093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1254481975221413798601457 940861481416060348951093)
                ·
                  refine ⟨88205763882755657714165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 940861481416060348951093 88205763882755657714165)
                  ·
                    rfl

theorem cell23_1546021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4, 2, 5].length) (baseStart_1546021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1546021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1546021 prefixEnd_1546021 := by exact prefixLift 1546021
  have htrace : WordTrace (prefixWord ++ tailWord_1546021) baseStart_1546021 baseEnd_1546021 := by
    simpa [prefixWord, tailWord_1546021, baseEnd_1546021] using wordTrace_append hprefix tailTrace_1546021
  have hstable : (prefixWord ++ tailWord_1546021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546021).length < 2 ^ (prefixWord ++ tailWord_1546021).sum := by decide
  have hdescent : baseEnd_1546021 < baseStart_1546021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546074 : List Nat := [3, 1, 1, 2, 1, 3, 2, 1, 4, 2, 3]
def baseStart_1546074 : Nat := 118140960795 + 1546074 * 2 ^ 59
def prefixEnd_1546074 : Nat := 4983230072969 + 3 ^ 40 * 1546074 * 2
def baseEnd_1546074 : Nat := 793879089419489212064741

theorem tailTrace_1546074 : CollatzResearch.WordTrace tailWord_1546074 prefixEnd_1546074 793879089419489212064741 := by
  unfold tailWord_1546074
  simp only [CollatzResearch.WordTrace]
  refine ⟨14097487850211355315585319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37593300933896947508227517 14097487850211355315585319)
  ·
    refine ⟨21146231775317032973377979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14097487850211355315585319 21146231775317032973377979)
    ·
      refine ⟨31719347662975549460066969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21146231775317032973377979 31719347662975549460066969)
      ·
        refine ⟨23789510747231662095050227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31719347662975549460066969 23789510747231662095050227)
        ·
          refine ⟨35684266120847493142575341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23789510747231662095050227 35684266120847493142575341)
          ·
            refine ⟨13381599795317809928465753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35684266120847493142575341 13381599795317809928465753)
            ·
              refine ⟨10036199846488357446349315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13381599795317809928465753 10036199846488357446349315)
              ·
                refine ⟨15054299769732536169523973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10036199846488357446349315 15054299769732536169523973)
                ·
                  refine ⟨2822681206824850531785745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15054299769732536169523973 2822681206824850531785745)
                  ·
                    refine ⟨2117010905118637898839309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2822681206824850531785745 2117010905118637898839309)
                    ·
                      refine ⟨793879089419489212064741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2117010905118637898839309 793879089419489212064741)
                      ·
                        rfl

theorem cell23_1546074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 4, 2, 3].length) (baseStart_1546074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1546074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1546074 prefixEnd_1546074 := by exact prefixLift 1546074
  have htrace : WordTrace (prefixWord ++ tailWord_1546074) baseStart_1546074 baseEnd_1546074 := by
    simpa [prefixWord, tailWord_1546074, baseEnd_1546074] using wordTrace_append hprefix tailTrace_1546074
  have hstable : (prefixWord ++ tailWord_1546074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546074).length < 2 ^ (prefixWord ++ tailWord_1546074).sum := by decide
  have hdescent : baseEnd_1546074 < baseStart_1546074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546081 : List Nat := [1, 2, 3, 1, 1, 1, 3, 6, 1, 4]
def baseStart_1546081 : Nat := 118140960795 + 1546081 * 2 ^ 59
def prefixEnd_1546081 : Nat := 4983230072969 + 3 ^ 40 * 1546081 * 2
def baseEnd_1546081 : Nat := 264627561261356894892403

theorem tailTrace_1546081 : CollatzResearch.WordTrace tailWord_1546081 prefixEnd_1546081 264627561261356894892403 := by
  unfold tailWord_1546081
  simp only [CollatzResearch.WordTrace]
  refine ⟨56390206711820061457846097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37593471141213374305230731 56390206711820061457846097)
  ·
    refine ⟨42292655033865046093384573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56390206711820061457846097 42292655033865046093384573)
    ·
      refine ⟨15859745637699392285019215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42292655033865046093384573 15859745637699392285019215)
      ·
        refine ⟨23789618456549088427528823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15859745637699392285019215 23789618456549088427528823)
        ·
          refine ⟨35684427684823632641293235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23789618456549088427528823 35684427684823632641293235)
          ·
            refine ⟨53526641527235448961939853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35684427684823632641293235 53526641527235448961939853)
            ·
              refine ⟨20072490572713293360727445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53526641527235448961939853 20072490572713293360727445)
              ·
                refine ⟨940897995595935626284099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20072490572713293360727445 940897995595935626284099)
                ·
                  refine ⟨1411346993393903439426149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 940897995595935626284099 1411346993393903439426149)
                  ·
                    refine ⟨264627561261356894892403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1411346993393903439426149 264627561261356894892403)
                    ·
                      rfl

theorem cell23_1546081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 6, 1, 4].length) (baseStart_1546081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1546081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1546081 prefixEnd_1546081 := by exact prefixLift 1546081
  have htrace : WordTrace (prefixWord ++ tailWord_1546081) baseStart_1546081 baseEnd_1546081 := by
    simpa [prefixWord, tailWord_1546081, baseEnd_1546081] using wordTrace_append hprefix tailTrace_1546081
  have hstable : (prefixWord ++ tailWord_1546081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546081).length < 2 ^ (prefixWord ++ tailWord_1546081).sum := by decide
  have hdescent : baseEnd_1546081 < baseStart_1546081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546097 : List Nat := [1, 2, 2, 2, 1, 3, 1, 2, 1, 2, 6]
def baseStart_1546097 : Nat := 118140960795 + 1546097 * 2 ^ 59
def prefixEnd_1546097 : Nat := 4983230072969 + 3 ^ 40 * 1546097 * 2
def baseEnd_1546097 : Nat := 793890899474542622077135

theorem tailTrace_1546097 : CollatzResearch.WordTrace tailWord_1546097 prefixEnd_1546097 793890899474542622077135 := by
  unfold tailWord_1546097
  simp only [CollatzResearch.WordTrace]
  refine ⟨56390790279762096190428545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37593860186508064126952363 56390790279762096190428545)
  ·
    refine ⟨42293092709821572142821409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56390790279762096190428545 42293092709821572142821409)
    ·
      refine ⟨31719819532366179107116057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42293092709821572142821409 31719819532366179107116057)
      ·
        refine ⟨23789864649274634330337043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31719819532366179107116057 23789864649274634330337043)
        ·
          refine ⟨35684796973911951495505565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23789864649274634330337043 35684796973911951495505565)
          ·
            refine ⟨13381798865216981810814587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35684796973911951495505565 13381798865216981810814587)
            ·
              refine ⟨20072698297825472716221881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13381798865216981810814587 20072698297825472716221881)
              ·
                refine ⟨15054523723369104537166411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20072698297825472716221881 15054523723369104537166411)
                ·
                  refine ⟨22581785585053656805749617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15054523723369104537166411 22581785585053656805749617)
                  ·
                    refine ⟨16936339188790242604312213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22581785585053656805749617 16936339188790242604312213)
                    ·
                      refine ⟨793890899474542622077135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16936339188790242604312213 793890899474542622077135)
                      ·
                        rfl

theorem cell23_1546097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_1546097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1546097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1546097 prefixEnd_1546097 := by exact prefixLift 1546097
  have htrace : WordTrace (prefixWord ++ tailWord_1546097) baseStart_1546097 baseEnd_1546097 := by
    simpa [prefixWord, tailWord_1546097, baseEnd_1546097] using wordTrace_append hprefix tailTrace_1546097
  have hstable : (prefixWord ++ tailWord_1546097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546097).length < 2 ^ (prefixWord ++ tailWord_1546097).sum := by decide
  have hdescent : baseEnd_1546097 < baseStart_1546097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546127 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 3, 7, 4]
def baseStart_1546127 : Nat := 118140960795 + 1546127 * 2 ^ 59
def prefixEnd_1546127 : Nat := 4983230072969 + 3 ^ 40 * 1546127 * 2
def baseEnd_1546127 : Nat := 793906303894177504701997

theorem tailTrace_1546127 : CollatzResearch.WordTrace tailWord_1546127 prefixEnd_1546127 793906303894177504701997 := by
  unfold tailWord_1546127
  simp only [CollatzResearch.WordTrace]
  refine ⟨56391884469653411314020635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37594589646435607542680423 56391884469653411314020635)
  ·
    refine ⟨84587826704480116971030953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56391884469653411314020635 84587826704480116971030953)
    ·
      refine ⟨63440870028360087728273215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84587826704480116971030953 63440870028360087728273215)
      ·
        refine ⟨95161305042540131592409823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63440870028360087728273215 95161305042540131592409823)
        ·
          refine ⟨142741957563810197388614735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95161305042540131592409823 142741957563810197388614735)
          ·
            refine ⟨214112936345715296082922103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142741957563810197388614735 214112936345715296082922103)
            ·
              refine ⟨321169404518572944124383155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214112936345715296082922103 321169404518572944124383155)
              ·
                refine ⟨481754106777859416186574733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 321169404518572944124383155 481754106777859416186574733)
                ·
                  refine ⟨180657790041697281069965525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 481754106777859416186574733 180657790041697281069965525)
                  ·
                    refine ⟨4234166954102280025077317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 180657790041697281069965525 4234166954102280025077317)
                    ·
                      refine ⟨793906303894177504701997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4234166954102280025077317 793906303894177504701997)
                      ·
                        rfl

theorem cell23_1546127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 7, 4].length) (baseStart_1546127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1546127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1546127 prefixEnd_1546127 := by exact prefixLift 1546127
  have htrace : WordTrace (prefixWord ++ tailWord_1546127) baseStart_1546127 baseEnd_1546127 := by
    simpa [prefixWord, tailWord_1546127, baseEnd_1546127] using wordTrace_append hprefix tailTrace_1546127
  have hstable : (prefixWord ++ tailWord_1546127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546127).length < 2 ^ (prefixWord ++ tailWord_1546127).sum := by decide
  have hdescent : baseEnd_1546127 < baseStart_1546127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546138 : List Nat := [3, 1, 1, 4, 2, 1, 3, 1, 3, 1, 3]
def baseStart_1546138 : Nat := 118140960795 + 1546138 * 2 ^ 59
def prefixEnd_1546138 : Nat := 4983230072969 + 3 ^ 40 * 1546138 * 2
def baseEnd_1546138 : Nat := 793911952181376961664447

theorem tailTrace_1546138 : CollatzResearch.WordTrace tailWord_1546138 prefixEnd_1546138 793911952181376961664447 := by
  unfold tailWord_1546138
  simp only [CollatzResearch.WordTrace]
  refine ⟨14098071418153390048167767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37594857115075706795114045 14098071418153390048167767)
  ·
    refine ⟨21147107127230085072251651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14098071418153390048167767 21147107127230085072251651)
    ·
      refine ⟨31720660690845127608377477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21147107127230085072251651 31720660690845127608377477)
      ·
        refine ⟨5947623879533461426570777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31720660690845127608377477 5947623879533461426570777)
        ·
          refine ⟨4460717909650096069928083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5947623879533461426570777 4460717909650096069928083)
          ·
            refine ⟨6691076864475144104892125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4460717909650096069928083 6691076864475144104892125)
            ·
              refine ⟨2509153824178179039334547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6691076864475144104892125 2509153824178179039334547)
              ·
                refine ⟨3763730736267268559001821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2509153824178179039334547 3763730736267268559001821)
                ·
                  refine ⟨1411399026100225709625683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3763730736267268559001821 1411399026100225709625683)
                  ·
                    refine ⟨2117098539150338564438525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1411399026100225709625683 2117098539150338564438525)
                    ·
                      refine ⟨793911952181376961664447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2117098539150338564438525 793911952181376961664447)
                      ·
                        rfl

theorem cell23_1546138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_1546138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1546138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1546138 prefixEnd_1546138 := by exact prefixLift 1546138
  have htrace : WordTrace (prefixWord ++ tailWord_1546138) baseStart_1546138 baseEnd_1546138 := by
    simpa [prefixWord, tailWord_1546138, baseEnd_1546138] using wordTrace_append hprefix tailTrace_1546138
  have hstable : (prefixWord ++ tailWord_1546138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546138).length < 2 ^ (prefixWord ++ tailWord_1546138).sum := by decide
  have hdescent : baseEnd_1546138 < baseStart_1546138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546144 : List Nat := [2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 4]
def baseStart_1546144 : Nat := 118140960795 + 1546144 * 2 ^ 59
def prefixEnd_1546144 : Nat := 4983230072969 + 3 ^ 40 * 1546144 * 2
def baseEnd_1546144 : Nat := 793915033065303938189419

theorem tailTrace_1546144 : CollatzResearch.WordTrace tailWord_1546144 prefixEnd_1546144 793915033065303938189419 := by
  unfold tailWord_1546144
  simp only [CollatzResearch.WordTrace]
  refine ⟨28196252255295911608694743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37595003007061215478259657 28196252255295911608694743)
  ·
    refine ⟨42294378382943867413042115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28196252255295911608694743 42294378382943867413042115)
    ·
      refine ⟨63441567574415801119563173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42294378382943867413042115 63441567574415801119563173)
      ·
        refine ⟨11895293920202962709918095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63441567574415801119563173 11895293920202962709918095)
        ·
          refine ⟨17842940880304444064877143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11895293920202962709918095 17842940880304444064877143)
          ·
            refine ⟨26764411320456666097315715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17842940880304444064877143 26764411320456666097315715)
            ·
              refine ⟨40146616980684999145973573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26764411320456666097315715 40146616980684999145973573)
              ·
                refine ⟨7527490683878437339870045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40146616980684999145973573 7527490683878437339870045)
                ·
                  refine ⟨2822809006454414002451267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7527490683878437339870045 2822809006454414002451267)
                  ·
                    refine ⟨4234213509681621003676901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2822809006454414002451267 4234213509681621003676901)
                    ·
                      refine ⟨793915033065303938189419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4234213509681621003676901 793915033065303938189419)
                      ·
                        rfl

theorem cell23_1546144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_1546144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1546144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1546144 prefixEnd_1546144 := by exact prefixLift 1546144
  have htrace : WordTrace (prefixWord ++ tailWord_1546144) baseStart_1546144 baseEnd_1546144 := by
    simpa [prefixWord, tailWord_1546144, baseEnd_1546144] using wordTrace_append hprefix tailTrace_1546144
  have hstable : (prefixWord ++ tailWord_1546144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546144).length < 2 ^ (prefixWord ++ tailWord_1546144).sum := by decide
  have hdescent : baseEnd_1546144 < baseStart_1546144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546145 : List Nat := [1, 2, 3, 4, 3, 1, 2, 1, 6]
def baseStart_1546145 : Nat := 118140960795 + 1546145 * 2 ^ 59
def prefixEnd_1546145 : Nat := 4983230072969 + 3 ^ 40 * 1546145 * 2
def baseEnd_1546145 : Nat := 88212838505106492697435

theorem tailTrace_1546145 : CollatzResearch.WordTrace tailWord_1546145 prefixEnd_1546145 88212838505106492697435 := by
  unfold tailWord_1546145
  simp only [CollatzResearch.WordTrace]
  refine ⟨56392540983588200388175889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37595027322392133592117259 56392540983588200388175889)
  ·
    refine ⟨42294405737691150291131917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56392540983588200388175889 42294405737691150291131917)
    ·
      refine ⟨15860402151634181359174469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42294405737691150291131917 15860402151634181359174469)
      ·
        refine ⟨2973825403431409004845213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15860402151634181359174469 2973825403431409004845213)
        ·
          refine ⟨1115184526286778376816955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2973825403431409004845213 1115184526286778376816955)
          ·
            refine ⟨1672776789430167565225433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1115184526286778376816955 1672776789430167565225433)
            ·
              refine ⟨1254582592072625673919075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1672776789430167565225433 1254582592072625673919075)
              ·
                refine ⟨1881873888108938510878613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1254582592072625673919075 1881873888108938510878613)
                ·
                  refine ⟨88212838505106492697435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1881873888108938510878613 88212838505106492697435)
                  ·
                    rfl

theorem cell23_1546145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 2, 1, 6].length) (baseStart_1546145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1546145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1546145 prefixEnd_1546145 := by exact prefixLift 1546145
  have htrace : WordTrace (prefixWord ++ tailWord_1546145) baseStart_1546145 baseEnd_1546145 := by
    simpa [prefixWord, tailWord_1546145, baseEnd_1546145] using wordTrace_append hprefix tailTrace_1546145
  have hstable : (prefixWord ++ tailWord_1546145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546145).length < 2 ^ (prefixWord ++ tailWord_1546145).sum := by decide
  have hdescent : baseEnd_1546145 < baseStart_1546145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546161 : List Nat := [1, 2, 2, 4, 2, 2, 1, 1, 3, 1, 4]
def baseStart_1546161 : Nat := 118140960795 + 1546161 * 2 ^ 59
def prefixEnd_1546161 : Nat := 4983230072969 + 3 ^ 40 * 1546161 * 2
def baseEnd_1546161 : Nat := 793923762236430371676841

theorem tailTrace_1546161 : CollatzResearch.WordTrace tailWord_1546161 prefixEnd_1546161 793923762236430371676841 := by
  unfold tailWord_1546161
  simp only [CollatzResearch.WordTrace]
  refine ⟨56393124551530235120758337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37595416367686823413838891 56393124551530235120758337)
  ·
    refine ⟨42294843413647676340568753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56393124551530235120758337 42294843413647676340568753)
    ·
      refine ⟨31721132560235757255426565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42294843413647676340568753 31721132560235757255426565)
      ·
        refine ⟨5947712355044204485392481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31721132560235757255426565 5947712355044204485392481)
        ·
          refine ⟨4460784266283153364044361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5947712355044204485392481 4460784266283153364044361)
          ·
            refine ⟨3345588199712365023033271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4460784266283153364044361 3345588199712365023033271)
            ·
              refine ⟨5018382299568547534549907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3345588199712365023033271 5018382299568547534549907)
              ·
                refine ⟨7527573449352821301824861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5018382299568547534549907 7527573449352821301824861)
                ·
                  refine ⟨2822840043507307988184323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7527573449352821301824861 2822840043507307988184323)
                  ·
                    refine ⟨4234260065260961982276485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2822840043507307988184323 4234260065260961982276485)
                    ·
                      refine ⟨793923762236430371676841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4234260065260961982276485 793923762236430371676841)
                      ·
                        rfl

theorem cell23_1546161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_1546161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1546161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1546161 prefixEnd_1546161 := by exact prefixLift 1546161
  have htrace : WordTrace (prefixWord ++ tailWord_1546161) baseStart_1546161 baseEnd_1546161 := by
    simpa [prefixWord, tailWord_1546161, baseEnd_1546161] using wordTrace_append hprefix tailTrace_1546161
  have hstable : (prefixWord ++ tailWord_1546161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546161).length < 2 ^ (prefixWord ++ tailWord_1546161).sum := by decide
  have hdescent : baseEnd_1546161 < baseStart_1546161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546188 : List Nat := [2, 2, 1, 4, 1, 3, 2, 2, 2, 4]
def baseStart_1546188 : Nat := 118140960795 + 1546188 * 2 ^ 59
def prefixEnd_1546188 : Nat := 4983230072969 + 3 ^ 40 * 1546188 * 2
def baseEnd_1546188 : Nat := 264645875404700588679739

theorem tailTrace_1546188 : CollatzResearch.WordTrace tailWord_1546188 prefixEnd_1546188 264645875404700588679739 := by
  unfold tailWord_1546188
  simp only [CollatzResearch.WordTrace]
  refine ⟨28197054661216209365995609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37596072881621612487994145 28197054661216209365995609)
  ·
    refine ⟨21147790995912157024496707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28197054661216209365995609 21147790995912157024496707)
    ·
      refine ⟨31721686493868235536745061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21147790995912157024496707 31721686493868235536745061)
      ·
        refine ⟨5947816217600294163139699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31721686493868235536745061 5947816217600294163139699)
        ·
          refine ⟨8921724326400441244709549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5947816217600294163139699 8921724326400441244709549)
          ·
            refine ⟨3345646622400165466766081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8921724326400441244709549 3345646622400165466766081)
            ·
              refine ⟨2509234966800124100074561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3345646622400165466766081 2509234966800124100074561)
              ·
                refine ⟨1881926225100093075055921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2509234966800124100074561 1881926225100093075055921)
                ·
                  refine ⟨1411444668825069806291941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1881926225100093075055921 1411444668825069806291941)
                  ·
                    refine ⟨264645875404700588679739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1411444668825069806291941 264645875404700588679739)
                    ·
                      rfl

theorem cell23_1546188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 2, 2, 4].length) (baseStart_1546188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1546188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1546188 prefixEnd_1546188 := by exact prefixLift 1546188
  have htrace : WordTrace (prefixWord ++ tailWord_1546188) baseStart_1546188 baseEnd_1546188 := by
    simpa [prefixWord, tailWord_1546188, baseEnd_1546188] using wordTrace_append hprefix tailTrace_1546188
  have hstable : (prefixWord ++ tailWord_1546188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546188).length < 2 ^ (prefixWord ++ tailWord_1546188).sum := by decide
  have hdescent : baseEnd_1546188 < baseStart_1546188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546201 : List Nat := [1, 2, 1, 2, 6, 2, 1, 8]
def baseStart_1546201 : Nat := 118140960795 + 1546201 * 2 ^ 59
def prefixEnd_1546201 : Nat := 4983230072969 + 3 ^ 40 * 1546201 * 2
def baseEnd_1546201 : Nat := 29405344498615193154691

theorem tailTrace_1546201 : CollatzResearch.WordTrace tailWord_1546201 prefixEnd_1546201 29405344498615193154691 := by
  unfold tailWord_1546201
  simp only [CollatzResearch.WordTrace]
  refine ⟨56394583471385321952214457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37596388980923547968142971 56394583471385321952214457)
  ·
    refine ⟨42295937603538991464160843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56394583471385321952214457 42295937603538991464160843)
    ·
      refine ⟨63443906405308487196241265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42295937603538991464160843 63443906405308487196241265)
      ·
        refine ⟨47582929803981365397180949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63443906405308487196241265 47582929803981365397180949)
        ·
          refine ⟨2230449834561626502992857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 47582929803981365397180949 2230449834561626502992857)
          ·
            refine ⟨1672837375921219877244643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2230449834561626502992857 1672837375921219877244643)
            ·
              refine ⟨2509256063881829815866965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1672837375921219877244643 2509256063881829815866965)
              ·
                refine ⟨29405344498615193154691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2509256063881829815866965 29405344498615193154691)
                ·
                  rfl

theorem cell23_1546201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 8].length) (baseStart_1546201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1546201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1546201 prefixEnd_1546201 := by exact prefixLift 1546201
  have htrace : WordTrace (prefixWord ++ tailWord_1546201) baseStart_1546201 baseEnd_1546201 := by
    simpa [prefixWord, tailWord_1546201, baseEnd_1546201] using wordTrace_append hprefix tailTrace_1546201
  have hstable : (prefixWord ++ tailWord_1546201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546201).length < 2 ^ (prefixWord ++ tailWord_1546201).sum := by decide
  have hdescent : baseEnd_1546201 < baseStart_1546201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546211 : List Nat := [1, 1, 1, 6, 1, 2, 1, 3, 1, 3, 3]
def baseStart_1546211 : Nat := 118140960795 + 1546211 * 2 ^ 59
def prefixEnd_1546211 : Nat := 4983230072969 + 3 ^ 40 * 1546211 * 2
def baseEnd_1546211 : Nat := 793949436269155176051611

theorem tailTrace_1546211 : CollatzResearch.WordTrace tailWord_1546211 prefixEnd_1546211 793949436269155176051611 := by
  unfold tailWord_1546211
  simp only [CollatzResearch.WordTrace]
  refine ⟨56394948201349093660078487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37596632134232729106718991 56394948201349093660078487)
  ·
    refine ⟨84592422302023640490117731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56394948201349093660078487 84592422302023640490117731)
    ·
      refine ⟨126888633453035460735176597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84592422302023640490117731 126888633453035460735176597)
      ·
        refine ⟨5947904693111037221961403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 126888633453035460735176597 5947904693111037221961403)
        ·
          refine ⟨8921857039666555832942105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5947904693111037221961403 8921857039666555832942105)
          ·
            refine ⟨6691392779749916874706579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8921857039666555832942105 6691392779749916874706579)
            ·
              refine ⟨10037089169624875312059869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6691392779749916874706579 10037089169624875312059869)
              ·
                refine ⟨3763908438609328242022451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10037089169624875312059869 3763908438609328242022451)
                ·
                  refine ⟨5645862657913992363033677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3763908438609328242022451 5645862657913992363033677)
                  ·
                    refine ⟨2117198496717747136137629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5645862657913992363033677 2117198496717747136137629)
                    ·
                      refine ⟨793949436269155176051611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2117198496717747136137629 793949436269155176051611)
                      ·
                        rfl

theorem cell23_1546211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_1546211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1546211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1546211 prefixEnd_1546211 := by exact prefixLift 1546211
  have htrace : WordTrace (prefixWord ++ tailWord_1546211) baseStart_1546211 baseEnd_1546211 := by
    simpa [prefixWord, tailWord_1546211, baseEnd_1546211] using wordTrace_append hprefix tailTrace_1546211
  have hstable : (prefixWord ++ tailWord_1546211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546211).length < 2 ^ (prefixWord ++ tailWord_1546211).sum := by decide
  have hdescent : baseEnd_1546211 < baseStart_1546211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546245 : List Nat := [1, 3, 1, 1, 2, 6, 1, 2, 2, 1, 3]
def baseStart_1546245 : Nat := 118140960795 + 1546245 * 2 ^ 59
def prefixEnd_1546245 : Nat := 4983230072969 + 3 ^ 40 * 1546245 * 2
def baseEnd_1546245 : Nat := 793966894611408043026455

theorem tailTrace_1546245 : CollatzResearch.WordTrace tailWord_1546245 prefixEnd_1546245 793966894611408043026455 := by
  unfold tailWord_1546245
  simp only [CollatzResearch.WordTrace]
  refine ⟨56396188283225917466816189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37597458855483944977877459 56396188283225917466816189)
  ·
    refine ⟨21148570606209719050056071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56396188283225917466816189 21148570606209719050056071)
    ·
      refine ⟨31722855909314578575084107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21148570606209719050056071 31722855909314578575084107)
      ·
        refine ⟨47584283863971867862626161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31722855909314578575084107 47584283863971867862626161)
        ·
          refine ⟨35688212897978900896969621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47584283863971867862626161 35688212897978900896969621)
          ·
            refine ⟨1672884979592760979545451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 35688212897978900896969621 1672884979592760979545451)
            ·
              refine ⟨2509327469389141469318177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1672884979592760979545451 2509327469389141469318177)
              ·
                refine ⟨1881995602041856101988633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2509327469389141469318177 1881995602041856101988633)
                ·
                  refine ⟨1411496701531392076491475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1881995602041856101988633 1411496701531392076491475)
                  ·
                    refine ⟨2117245052297088114737213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1411496701531392076491475 2117245052297088114737213)
                    ·
                      refine ⟨793966894611408043026455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2117245052297088114737213 793966894611408043026455)
                      ·
                        rfl

theorem cell23_1546245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 2, 2, 1, 3].length) (baseStart_1546245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1546245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1546245 prefixEnd_1546245 := by exact prefixLift 1546245
  have htrace : WordTrace (prefixWord ++ tailWord_1546245) baseStart_1546245 baseEnd_1546245 := by
    simpa [prefixWord, tailWord_1546245, baseEnd_1546245] using wordTrace_append hprefix tailTrace_1546245
  have hstable : (prefixWord ++ tailWord_1546245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546245).length < 2 ^ (prefixWord ++ tailWord_1546245).sum := by decide
  have hdescent : baseEnd_1546245 < baseStart_1546245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546392 : List Nat := [2, 1, 2, 4, 4, 1, 1, 1, 2, 1, 4]
def baseStart_1546392 : Nat := 118140960795 + 1546392 * 2 ^ 59
def prefixEnd_1546392 : Nat := 4983230072969 + 3 ^ 40 * 1546392 * 2
def baseEnd_1546392 : Nat := 794042376267618967888279

theorem tailTrace_1546392 : CollatzResearch.WordTrace tailWord_1546392 prefixEnd_1546392 794042376267618967888279 := by
  unfold tailWord_1546392
  simp only [CollatzResearch.WordTrace]
  refine ⟨28200774906846680786208715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37601033209128907714944953 28200774906846680786208715)
  ·
    refine ⟨42301162360270021179313073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28200774906846680786208715 42301162360270021179313073)
    ·
      refine ⟨31725871770202515884484805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42301162360270021179313073 31725871770202515884484805)
      ·
        refine ⟨5948600956912971728340901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31725871770202515884484805 5948600956912971728340901)
        ·
          refine ⟨1115362679421182199063919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5948600956912971728340901 1115362679421182199063919)
          ·
            refine ⟨1673044019131773298595879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1115362679421182199063919 1673044019131773298595879)
            ·
              refine ⟨2509566028697659947893819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1673044019131773298595879 2509566028697659947893819)
              ·
                refine ⟨3764349043046489921840729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2509566028697659947893819 3764349043046489921840729)
                ·
                  refine ⟨2823261782284867441380547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3764349043046489921840729 2823261782284867441380547)
                  ·
                    refine ⟨4234892673427301162070821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2823261782284867441380547 4234892673427301162070821)
                    ·
                      refine ⟨794042376267618967888279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4234892673427301162070821 794042376267618967888279)
                      ·
                        rfl

theorem cell23_1546392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_1546392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1546392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1546392 prefixEnd_1546392 := by exact prefixLift 1546392
  have htrace : WordTrace (prefixWord ++ tailWord_1546392) baseStart_1546392 baseEnd_1546392 := by
    simpa [prefixWord, tailWord_1546392, baseEnd_1546392] using wordTrace_append hprefix tailTrace_1546392
  have hstable : (prefixWord ++ tailWord_1546392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546392).length < 2 ^ (prefixWord ++ tailWord_1546392).sum := by decide
  have hdescent : baseEnd_1546392 < baseStart_1546392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546402 : List Nat := [3, 3, 1, 3, 1, 1, 1, 5, 1, 4]
def baseStart_1546402 : Nat := 118140960795 + 1546402 * 2 ^ 59
def prefixEnd_1546402 : Nat := 4983230072969 + 3 ^ 40 * 1546402 * 2
def baseEnd_1546402 : Nat := 264682503691387976254411

theorem tailTrace_1546402 : CollatzResearch.WordTrace tailWord_1546402 prefixEnd_1546402 264682503691387976254411 := by
  unfold tailWord_1546402
  simp only [CollatzResearch.WordTrace]
  refine ⟨14100478635914283320070365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37601276362438088853520973 14100478635914283320070365)
  ·
    refine ⟨5287679488467856245026387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14100478635914283320070365 5287679488467856245026387)
    ·
      refine ⟨7931519232701784367539581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5287679488467856245026387 7931519232701784367539581)
      ·
        refine ⟨2974319712263169137827343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7931519232701784367539581 2974319712263169137827343)
        ·
          refine ⟨4461479568394753706741015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2974319712263169137827343 4461479568394753706741015)
          ·
            refine ⟨6692219352592130560111523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4461479568394753706741015 6692219352592130560111523)
            ·
              refine ⟨10038329028888195840167285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6692219352592130560111523 10038329028888195840167285)
              ·
                refine ⟨941093346458268360015683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10038329028888195840167285 941093346458268360015683)
                ·
                  refine ⟨1411640019687402540023525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 941093346458268360015683 1411640019687402540023525)
                  ·
                    refine ⟨264682503691387976254411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1411640019687402540023525 264682503691387976254411)
                    ·
                      rfl

theorem cell23_1546402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 5, 1, 4].length) (baseStart_1546402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1546402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1546402 prefixEnd_1546402 := by exact prefixLift 1546402
  have htrace : WordTrace (prefixWord ++ tailWord_1546402) baseStart_1546402 baseEnd_1546402 := by
    simpa [prefixWord, tailWord_1546402, baseEnd_1546402] using wordTrace_append hprefix tailTrace_1546402
  have hstable : (prefixWord ++ tailWord_1546402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546402).length < 2 ^ (prefixWord ++ tailWord_1546402).sum := by decide
  have hdescent : baseEnd_1546402 < baseStart_1546402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546425 : List Nat := [1, 2, 1, 4, 1, 2, 4, 1, 3, 1, 3]
def baseStart_1546425 : Nat := 118140960795 + 1546425 * 2 ^ 59
def prefixEnd_1546425 : Nat := 4983230072969 + 3 ^ 40 * 1546425 * 2
def baseEnd_1546425 : Nat := 794059321129217338775627

theorem tailTrace_1546425 : CollatzResearch.WordTrace tailWord_1546425 prefixEnd_1546425 794059321129217338775627 := by
  unfold tailWord_1546425
  simp only [CollatzResearch.WordTrace]
  refine ⟨56402753422573808208368729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37601835615049205472245819 56402753422573808208368729)
  ·
    refine ⟨42302065066930356156276547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56402753422573808208368729 42302065066930356156276547)
    ·
      refine ⟨63453097600395534234414821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42302065066930356156276547 63453097600395534234414821)
      ·
        refine ⟨11897455800074162668952779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63453097600395534234414821 11897455800074162668952779)
        ·
          refine ⟨17846183700111244003429169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11897455800074162668952779 17846183700111244003429169)
          ·
            refine ⟨13384637775083433002571877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17846183700111244003429169 13384637775083433002571877)
            ·
              refine ⟨2509619582828143687982227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13384637775083433002571877 2509619582828143687982227)
              ·
                refine ⟨3764429374242215531973341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2509619582828143687982227 3764429374242215531973341)
                ·
                  refine ⟨1411661015340830824490003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3764429374242215531973341 1411661015340830824490003)
                  ·
                    refine ⟨2117491523011246236735005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1411661015340830824490003 2117491523011246236735005)
                    ·
                      refine ⟨794059321129217338775627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2117491523011246236735005 794059321129217338775627)
                      ·
                        rfl

theorem cell23_1546425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 1, 3, 1, 3].length) (baseStart_1546425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1546425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1546425 prefixEnd_1546425 := by exact prefixLift 1546425
  have htrace : WordTrace (prefixWord ++ tailWord_1546425) baseStart_1546425 baseEnd_1546425 := by
    simpa [prefixWord, tailWord_1546425, baseEnd_1546425] using wordTrace_append hprefix tailTrace_1546425
  have hstable : (prefixWord ++ tailWord_1546425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546425).length < 2 ^ (prefixWord ++ tailWord_1546425).sum := by decide
  have hdescent : baseEnd_1546425 < baseStart_1546425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546441 : List Nat := [1, 2, 1, 1, 2, 1, 1, 7, 1, 6]
def baseStart_1546441 : Nat := 118140960795 + 1546441 * 2 ^ 59
def prefixEnd_1546441 : Nat := 4983230072969 + 3 ^ 40 * 1546441 * 2
def baseEnd_1546441 : Nat := 264689178939896425391851

theorem tailTrace_1546441 : CollatzResearch.WordTrace tailWord_1546441 prefixEnd_1546441 264689178939896425391851 := by
  unfold tailWord_1546441
  simp only [CollatzResearch.WordTrace]
  refine ⟨56403336990515842940951177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37602224660343895293967451 56403336990515842940951177)
  ·
    refine ⟨42302502742886882205713383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56403336990515842940951177 42302502742886882205713383)
    ·
      refine ⟨63453754114330323308570075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42302502742886882205713383 63453754114330323308570075)
      ·
        refine ⟨95180631171495484962855113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63453754114330323308570075 95180631171495484962855113)
        ·
          refine ⟨71385473378621613722141335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95180631171495484962855113 71385473378621613722141335)
          ·
            refine ⟨107078210067932420583212003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71385473378621613722141335 107078210067932420583212003)
            ·
              refine ⟨160617315101898630874818005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107078210067932420583212003 160617315101898630874818005)
              ·
                refine ⟨3764468322700749161128547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 160617315101898630874818005 3764468322700749161128547)
                ·
                  refine ⟨5646702484051123741692821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3764468322700749161128547 5646702484051123741692821)
                  ·
                    refine ⟨264689178939896425391851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5646702484051123741692821 264689178939896425391851)
                    ·
                      rfl

theorem cell23_1546441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7, 1, 6].length) (baseStart_1546441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1546441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1546441 prefixEnd_1546441 := by exact prefixLift 1546441
  have htrace : WordTrace (prefixWord ++ tailWord_1546441) baseStart_1546441 baseEnd_1546441 := by
    simpa [prefixWord, tailWord_1546441, baseEnd_1546441] using wordTrace_append hprefix tailTrace_1546441
  have hstable : (prefixWord ++ tailWord_1546441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546441).length < 2 ^ (prefixWord ++ tailWord_1546441).sum := by decide
  have hdescent : baseEnd_1546441 < baseStart_1546441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546458 : List Nat := [3, 1, 1, 2, 2, 1, 3, 2, 4, 4]
def baseStart_1546458 : Nat := 118140960795 + 1546458 * 2 ^ 59
def prefixEnd_1546458 : Nat := 4983230072969 + 3 ^ 40 * 1546458 * 2
def baseEnd_1546458 : Nat := 264692088663605236554325

theorem tailTrace_1546458 : CollatzResearch.WordTrace tailWord_1546458 prefixEnd_1546458 264692088663605236554325 := by
  unfold tailWord_1546458
  simp only [CollatzResearch.WordTrace]
  refine ⟨14100989257863563711080007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37602638020969503229546685 14100989257863563711080007)
  ·
    refine ⟨21151483886795345566620011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14100989257863563711080007 21151483886795345566620011)
    ·
      refine ⟨31727225830193018349930017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21151483886795345566620011 31727225830193018349930017)
      ·
        refine ⟨23795419372644763762447513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31727225830193018349930017 23795419372644763762447513)
        ·
          refine ⟨17846564529483572821835635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23795419372644763762447513 17846564529483572821835635)
          ·
            refine ⟨26769846794225359232753453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17846564529483572821835635 26769846794225359232753453)
            ·
              refine ⟨10038692547834509712282545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26769846794225359232753453 10038692547834509712282545)
              ·
                refine ⟨7529019410875882284211909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10038692547834509712282545 7529019410875882284211909)
                ·
                  refine ⟨1411691139539227928289733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7529019410875882284211909 1411691139539227928289733)
                  ·
                    refine ⟨264692088663605236554325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1411691139539227928289733 264692088663605236554325)
                    ·
                      rfl

theorem cell23_1546458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 4, 4].length) (baseStart_1546458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1546458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1546458 prefixEnd_1546458 := by exact prefixLift 1546458
  have htrace : WordTrace (prefixWord ++ tailWord_1546458) baseStart_1546458 baseEnd_1546458 := by
    simpa [prefixWord, tailWord_1546458, baseEnd_1546458] using wordTrace_append hprefix tailTrace_1546458
  have hstable : (prefixWord ++ tailWord_1546458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546458).length < 2 ^ (prefixWord ++ tailWord_1546458).sum := by decide
  have hdescent : baseEnd_1546458 < baseStart_1546458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546468 : List Nat := [2, 3, 1, 1, 1, 2, 1, 2, 5, 2, 3]
def baseStart_1546468 : Nat := 118140960795 + 1546468 * 2 ^ 59
def prefixEnd_1546468 : Nat := 4983230072969 + 3 ^ 40 * 1546468 * 2
def baseEnd_1546468 : Nat := 794081400797360670537929

theorem tailTrace_1546468 : CollatzResearch.WordTrace tailWord_1546468 prefixEnd_1546468 794081400797360670537929 := by
  unfold tailWord_1546468
  simp only [CollatzResearch.WordTrace]
  refine ⟨28202160880709013276092029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37602881174278684368122705 28202160880709013276092029)
  ·
    refine ⟨10575810330265879978534511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28202160880709013276092029 10575810330265879978534511)
    ·
      refine ⟨15863715495398819967801767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10575810330265879978534511 15863715495398819967801767)
      ·
        refine ⟨23795573243098229951702651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15863715495398819967801767 23795573243098229951702651)
        ·
          refine ⟨35693359864647344927553977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23795573243098229951702651 35693359864647344927553977)
          ·
            refine ⟨26770019898485508695665483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35693359864647344927553977 26770019898485508695665483)
            ·
              refine ⟨40155029847728263043498225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26770019898485508695665483 40155029847728263043498225)
              ·
                refine ⟨30116272385796197282623669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40155029847728263043498225 30116272385796197282623669)
                ·
                  refine ⟨2823400536168393495245969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30116272385796197282623669 2823400536168393495245969)
                  ·
                    refine ⟨2117550402126295121434477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2823400536168393495245969 2117550402126295121434477)
                    ·
                      refine ⟨794081400797360670537929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2117550402126295121434477 794081400797360670537929)
                      ·
                        rfl

theorem cell23_1546468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 5, 2, 3].length) (baseStart_1546468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1546468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1546468 prefixEnd_1546468 := by exact prefixLift 1546468
  have htrace : WordTrace (prefixWord ++ tailWord_1546468) baseStart_1546468 baseEnd_1546468 := by
    simpa [prefixWord, tailWord_1546468, baseEnd_1546468] using wordTrace_append hprefix tailTrace_1546468
  have hstable : (prefixWord ++ tailWord_1546468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546468).length < 2 ^ (prefixWord ++ tailWord_1546468).sum := by decide
  have hdescent : baseEnd_1546468 < baseStart_1546468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546492 : List Nat := [2, 2, 2, 1, 4, 1, 4, 1, 2, 4]
def baseStart_1546492 : Nat := 118140960795 + 1546492 * 2 ^ 59
def prefixEnd_1546492 : Nat := 4983230072969 + 3 ^ 40 * 1546492 * 2
def baseEnd_1546492 : Nat := 264697908111022858879273

theorem tailTrace_1546492 : CollatzResearch.WordTrace tailWord_1546492 prefixEnd_1546492 264697908111022858879273 := by
  unfold tailWord_1546492
  simp only [CollatzResearch.WordTrace]
  refine ⟨28202598556665539325528865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37603464742220719100705153 28202598556665539325528865)
  ·
    refine ⟨21151948917499154494146649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28202598556665539325528865 21151948917499154494146649)
    ·
      refine ⟨15863961688124365870609987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21151948917499154494146649 15863961688124365870609987)
      ·
        refine ⟨23795942532186548805914981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15863961688124365870609987 23795942532186548805914981)
        ·
          refine ⟨4461739224784977901109059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23795942532186548805914981 4461739224784977901109059)
          ·
            refine ⟨6692608837177466851663589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4461739224784977901109059 6692608837177466851663589)
            ·
              refine ⟨1254864156970775034686923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6692608837177466851663589 1254864156970775034686923)
              ·
                refine ⟨1882296235456162552030385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1254864156970775034686923 1882296235456162552030385)
                ·
                  refine ⟨1411722176592121914022789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1882296235456162552030385 1411722176592121914022789)
                  ·
                    refine ⟨264697908111022858879273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1411722176592121914022789 264697908111022858879273)
                    ·
                      rfl

theorem cell23_1546492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4, 1, 2, 4].length) (baseStart_1546492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1546492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1546492 prefixEnd_1546492 := by exact prefixLift 1546492
  have htrace : WordTrace (prefixWord ++ tailWord_1546492) baseStart_1546492 baseEnd_1546492 := by
    simpa [prefixWord, tailWord_1546492, baseEnd_1546492] using wordTrace_append hprefix tailTrace_1546492
  have hstable : (prefixWord ++ tailWord_1546492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546492).length < 2 ^ (prefixWord ++ tailWord_1546492).sum := by decide
  have hdescent : baseEnd_1546492 < baseStart_1546492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546501 : List Nat := [1, 3, 1, 1, 2, 1, 2, 1, 4, 7]
def baseStart_1546501 : Nat := 118140960795 + 1546501 * 2 ^ 59
def prefixEnd_1546501 : Nat := 4983230072969 + 3 ^ 40 * 1546501 * 2
def baseEnd_1546501 : Nat := 264699448552986347141759

theorem tailTrace_1546501 : CollatzResearch.WordTrace tailWord_1546501 prefixEnd_1546501 264699448552986347141759 := by
  unfold tailWord_1546501
  simp only [CollatzResearch.WordTrace]
  refine ⟨56405525370298473188135357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37603683580198982125423571 56405525370298473188135357)
  ·
    refine ⟨21152072013861927445550759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56405525370298473188135357 21152072013861927445550759)
    ·
      refine ⟨31728108020792891168326139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21152072013861927445550759 31728108020792891168326139)
      ·
        refine ⟨47592162031189336752489209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31728108020792891168326139 47592162031189336752489209)
        ·
          refine ⟨35694121523392002564366907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47592162031189336752489209 35694121523392002564366907)
          ·
            refine ⟨53541182285088003846550361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35694121523392002564366907 53541182285088003846550361)
            ·
              refine ⟨40155886713816002884912771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53541182285088003846550361 40155886713816002884912771)
              ·
                refine ⟨60233830070724004327369157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40155886713816002884912771 60233830070724004327369157)
                ·
                  refine ⟨11293843138260750811381717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60233830070724004327369157 11293843138260750811381717)
                  ·
                    refine ⟨264699448552986347141759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11293843138260750811381717 264699448552986347141759)
                    ·
                      rfl

theorem cell23_1546501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 7].length) (baseStart_1546501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1546501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1546501 prefixEnd_1546501 := by exact prefixLift 1546501
  have htrace : WordTrace (prefixWord ++ tailWord_1546501) baseStart_1546501 baseEnd_1546501 := by
    simpa [prefixWord, tailWord_1546501, baseEnd_1546501] using wordTrace_append hprefix tailTrace_1546501
  have hstable : (prefixWord ++ tailWord_1546501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546501).length < 2 ^ (prefixWord ++ tailWord_1546501).sum := by decide
  have hdescent : baseEnd_1546501 < baseStart_1546501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546511 : List Nat := [1, 1, 2, 1, 1, 1, 3, 3, 1, 4, 5]
def baseStart_1546511 : Nat := 118140960795 + 1546511 * 2 ^ 59
def prefixEnd_1546511 : Nat := 4983230072969 + 3 ^ 40 * 1546511 * 2
def baseEnd_1546511 : Nat := 794103480465504002300231

theorem tailTrace_1546511 : CollatzResearch.WordTrace tailWord_1546511 prefixEnd_1546511 794103480465504002300231 := by
  unfold tailWord_1546511
  simp only [CollatzResearch.WordTrace]
  refine ⟨56405890100262244895999387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37603926733508163263999591 56405890100262244895999387)
  ·
    refine ⟨84608835150393367343999081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56405890100262244895999387 84608835150393367343999081)
    ·
      refine ⟨63456626362795025507999311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84608835150393367343999081 63456626362795025507999311)
      ·
        refine ⟨95184939544192538261998967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63456626362795025507999311 95184939544192538261998967)
        ·
          refine ⟨142777409316288807392998451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95184939544192538261998967 142777409316288807392998451)
          ·
            refine ⟨214166113974433211089497677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142777409316288807392998451 214166113974433211089497677)
            ·
              refine ⟨80312292740412454158561629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 214166113974433211089497677 80312292740412454158561629)
              ·
                refine ⟨30117109777654670309460611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80312292740412454158561629 30117109777654670309460611)
                ·
                  refine ⟨45175664666482005464190917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30117109777654670309460611 45175664666482005464190917)
                  ·
                    refine ⟨8470437124965376024535797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45175664666482005464190917 8470437124965376024535797)
                    ·
                      refine ⟨794103480465504002300231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8470437124965376024535797 794103480465504002300231)
                      ·
                        rfl

theorem cell23_1546511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4, 5].length) (baseStart_1546511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1546511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1546511 prefixEnd_1546511 := by exact prefixLift 1546511
  have htrace : WordTrace (prefixWord ++ tailWord_1546511) baseStart_1546511 baseEnd_1546511 := by
    simpa [prefixWord, tailWord_1546511, baseEnd_1546511] using wordTrace_append hprefix tailTrace_1546511
  have hstable : (prefixWord ++ tailWord_1546511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546511).length < 2 ^ (prefixWord ++ tailWord_1546511).sum := by decide
  have hdescent : baseEnd_1546511 < baseStart_1546511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546532 : List Nat := [2, 3, 1, 3, 1, 2, 1, 4, 2, 1, 3]
def baseStart_1546532 : Nat := 118140960795 + 1546532 * 2 ^ 59
def prefixEnd_1546532 : Nat := 4983230072969 + 3 ^ 40 * 1546532 * 2
def baseEnd_1546532 : Nat := 794114263559248420137635

theorem tailTrace_1546532 : CollatzResearch.WordTrace tailWord_1546532 prefixEnd_1546532 794114263559248420137635 := by
  unfold tailWord_1546532
  simp only [CollatzResearch.WordTrace]
  refine ⟨28203328016593082741256925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37604437355457443655009233 28203328016593082741256925)
  ·
    refine ⟨10576248006222406027971347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28203328016593082741256925 10576248006222406027971347)
    ·
      refine ⟨15864372009333609041957021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10576248006222406027971347 15864372009333609041957021)
      ·
        refine ⟨5949139503500103390733883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15864372009333609041957021 5949139503500103390733883)
        ·
          refine ⟨8923709255250155086100825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5949139503500103390733883 8923709255250155086100825)
          ·
            refine ⟨6692781941437616314575619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8923709255250155086100825 6692781941437616314575619)
            ·
              refine ⟨10039172912156424471863429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6692781941437616314575619 10039172912156424471863429)
              ·
                refine ⟨1882344921029329588474393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10039172912156424471863429 1882344921029329588474393)
                ·
                  refine ⟨1411758690771997191355795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1882344921029329588474393 1411758690771997191355795)
                  ·
                    refine ⟨2117638036157995787033693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1411758690771997191355795 2117638036157995787033693)
                    ·
                      refine ⟨794114263559248420137635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2117638036157995787033693 794114263559248420137635)
                      ·
                        rfl

theorem cell23_1546532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_1546532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1546532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1546532 prefixEnd_1546532 := by exact prefixLift 1546532
  have htrace : WordTrace (prefixWord ++ tailWord_1546532) baseStart_1546532 baseEnd_1546532 := by
    simpa [prefixWord, tailWord_1546532, baseEnd_1546532] using wordTrace_append hprefix tailTrace_1546532
  have hstable : (prefixWord ++ tailWord_1546532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546532).length < 2 ^ (prefixWord ++ tailWord_1546532).sum := by decide
  have hdescent : baseEnd_1546532 < baseStart_1546532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546533 : List Nat := [1, 3, 1, 2, 5, 2, 2, 2, 1, 2, 2]
def baseStart_1546533 : Nat := 118140960795 + 1546533 * 2 ^ 59
def prefixEnd_1546533 : Nat := 4983230072969 + 3 ^ 40 * 1546533 * 2
def baseEnd_1546533 : Nat := 794114777039902916225131

theorem tailTrace_1546533 : CollatzResearch.WordTrace tailWord_1546533 prefixEnd_1546533 794114777039902916225131 := by
  unfold tailWord_1546533
  simp only [CollatzResearch.WordTrace]
  refine ⟨56406692506182542653300253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37604461670788361768866835 56406692506182542653300253)
  ·
    refine ⟨21152509689818453494987595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56406692506182542653300253 21152509689818453494987595)
    ·
      refine ⟨31728764534727680242481393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21152509689818453494987595 31728764534727680242481393)
      ·
        refine ⟨23796573401045760181861045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31728764534727680242481393 23796573401045760181861045)
        ·
          refine ⟨2230928756348040017049473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23796573401045760181861045 2230928756348040017049473)
          ·
            refine ⟨1673196567261030012787105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2230928756348040017049473 1673196567261030012787105)
            ·
              refine ⟨1254897425445772509590329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1673196567261030012787105 1254897425445772509590329)
              ·
                refine ⟨941173069084329382192747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1254897425445772509590329 941173069084329382192747)
                ·
                  refine ⟨1411759603626494073289121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 941173069084329382192747 1411759603626494073289121)
                  ·
                    refine ⟨1058819702719870554966841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1411759603626494073289121 1058819702719870554966841)
                    ·
                      refine ⟨794114777039902916225131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1058819702719870554966841 794114777039902916225131)
                      ·
                        rfl

theorem cell23_1546533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2, 2, 1, 2, 2].length) (baseStart_1546533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1546533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1546533 prefixEnd_1546533 := by exact prefixLift 1546533
  have htrace : WordTrace (prefixWord ++ tailWord_1546533) baseStart_1546533 baseEnd_1546533 := by
    simpa [prefixWord, tailWord_1546533, baseEnd_1546533] using wordTrace_append hprefix tailTrace_1546533
  have hstable : (prefixWord ++ tailWord_1546533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546533).length < 2 ^ (prefixWord ++ tailWord_1546533).sum := by decide
  have hdescent : baseEnd_1546533 < baseStart_1546533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546572 : List Nat := [2, 2, 1, 3, 2, 1, 2, 2, 4, 2, 2]
def baseStart_1546572 : Nat := 118140960795 + 1546572 * 2 ^ 59
def prefixEnd_1546572 : Nat := 4983230072969 + 3 ^ 40 * 1546572 * 2
def baseEnd_1546572 : Nat := 794134802785428263637451

theorem tailTrace_1546572 : CollatzResearch.WordTrace tailWord_1546572 prefixEnd_1546572 794134802785428263637451 := by
  unfold tailWord_1546572
  simp only [CollatzResearch.WordTrace]
  refine ⟨28204057476520626156984985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37605409968694168209313313 28204057476520626156984985)
  ·
    refine ⟨21153043107390469617738739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28204057476520626156984985 21153043107390469617738739)
    ·
      refine ⟨31729564661085704426608109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21153043107390469617738739 31729564661085704426608109)
      ·
        refine ⟨11898586747907139159978041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31729564661085704426608109 11898586747907139159978041)
        ·
          refine ⟨8923940060930354369983531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11898586747907139159978041 8923940060930354369983531)
          ·
            refine ⟨13385910091395531554975297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8923940060930354369983531 13385910091395531554975297)
            ·
              refine ⟨10039432568546648666231473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13385910091395531554975297 10039432568546648666231473)
              ·
                refine ⟨7529574426409986499673605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10039432568546648666231473 7529574426409986499673605)
                ·
                  refine ⟨1411795204951872468688801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7529574426409986499673605 1411795204951872468688801)
                  ·
                    refine ⟨1058846403713904351516601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1411795204951872468688801 1058846403713904351516601)
                    ·
                      refine ⟨794134802785428263637451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1058846403713904351516601 794134802785428263637451)
                      ·
                        rfl

theorem cell23_1546572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 4, 2, 2].length) (baseStart_1546572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1546572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1546572 prefixEnd_1546572 := by exact prefixLift 1546572
  have htrace : WordTrace (prefixWord ++ tailWord_1546572) baseStart_1546572 baseEnd_1546572 := by
    simpa [prefixWord, tailWord_1546572, baseEnd_1546572] using wordTrace_append hprefix tailTrace_1546572
  have hstable : (prefixWord ++ tailWord_1546572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546572).length < 2 ^ (prefixWord ++ tailWord_1546572).sum := by decide
  have hdescent : baseEnd_1546572 < baseStart_1546572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546595 : List Nat := [1, 1, 1, 5, 2, 1, 1, 6, 5]
def baseStart_1546595 : Nat := 118140960795 + 1546595 * 2 ^ 59
def prefixEnd_1546595 : Nat := 4983230072969 + 3 ^ 40 * 1546595 * 2
def baseEnd_1546595 : Nat := 88238512537831297072205

theorem tailTrace_1546595 : CollatzResearch.WordTrace tailWord_1546595 prefixEnd_1546595 88238512537831297072205 := by
  unfold tailWord_1546595
  simp only [CollatzResearch.WordTrace]
  refine ⟨56408953831957927242057239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37605969221305284828038159 56408953831957927242057239)
  ·
    refine ⟨84613430747936890863085859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56408953831957927242057239 84613430747936890863085859)
    ·
      refine ⟨126920146121905336294628789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84613430747936890863085859 126920146121905336294628789)
      ·
        refine ⟨11898763698928625277621449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 126920146121905336294628789 11898763698928625277621449)
        ·
          refine ⟨8924072774196468958216087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11898763698928625277621449 8924072774196468958216087)
          ·
            refine ⟨13386109161294703437324131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8924072774196468958216087 13386109161294703437324131)
            ·
              refine ⟨20079163741942055155986197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13386109161294703437324131 20079163741942055155986197)
              ·
                refine ⟨941210800403533835436853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20079163741942055155986197 941210800403533835436853)
                ·
                  refine ⟨88238512537831297072205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 941210800403533835436853 88238512537831297072205)
                  ·
                    rfl

theorem cell23_1546595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 6, 5].length) (baseStart_1546595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1546595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1546595 prefixEnd_1546595 := by exact prefixLift 1546595
  have htrace : WordTrace (prefixWord ++ tailWord_1546595) baseStart_1546595 baseEnd_1546595 := by
    simpa [prefixWord, tailWord_1546595, baseEnd_1546595] using wordTrace_append hprefix tailTrace_1546595
  have hstable : (prefixWord ++ tailWord_1546595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546595).length < 2 ^ (prefixWord ++ tailWord_1546595).sum := by decide
  have hdescent : baseEnd_1546595 < baseStart_1546595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546605 : List Nat := [1, 5, 1, 1, 1, 2, 1, 3, 2, 3, 3]
def baseStart_1546605 : Nat := 118140960795 + 1546605 * 2 ^ 59
def prefixEnd_1546605 : Nat := 4983230072969 + 3 ^ 40 * 1546605 * 2
def baseEnd_1546605 : Nat := 794151747647026634524799

theorem tailTrace_1546605 : CollatzResearch.WordTrace tailWord_1546605 prefixEnd_1546605 794151747647026634524799 := by
  unfold tailWord_1546605
  simp only [CollatzResearch.WordTrace]
  refine ⟨56409318561921698949921269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37606212374614465966614179 56409318561921698949921269)
  ·
    refine ⟨5288373615180159276555119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56409318561921698949921269 5288373615180159276555119)
    ·
      refine ⟨7932560422770238914832679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5288373615180159276555119 7932560422770238914832679)
      ·
        refine ⟨11898840634155358372249019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7932560422770238914832679 11898840634155358372249019)
        ·
          refine ⟨17848260951233037558373529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11898840634155358372249019 17848260951233037558373529)
          ·
            refine ⟨13386195713424778168780147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17848260951233037558373529 13386195713424778168780147)
            ·
              refine ⟨20079293570137167253170221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13386195713424778168780147 20079293570137167253170221)
              ·
                refine ⟨7529735088801437719938833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20079293570137167253170221 7529735088801437719938833)
                ·
                  refine ⟨5647301316601078289954125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7529735088801437719938833 5647301316601078289954125)
                  ·
                    refine ⟨2117737993725404358732797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5647301316601078289954125 2117737993725404358732797)
                    ·
                      refine ⟨794151747647026634524799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2117737993725404358732797 794151747647026634524799)
                      ·
                        rfl

theorem cell23_1546605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_1546605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1546605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1546605 prefixEnd_1546605 := by exact prefixLift 1546605
  have htrace : WordTrace (prefixWord ++ tailWord_1546605) baseStart_1546605 baseEnd_1546605 := by
    simpa [prefixWord, tailWord_1546605, baseEnd_1546605] using wordTrace_append hprefix tailTrace_1546605
  have hstable : (prefixWord ++ tailWord_1546605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546605).length < 2 ^ (prefixWord ++ tailWord_1546605).sum := by decide
  have hdescent : baseEnd_1546605 < baseStart_1546605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546608 : List Nat := [2, 1, 1, 1, 4, 3, 1, 2, 1, 7]
def baseStart_1546608 : Nat := 118140960795 + 1546608 * 2 ^ 59
def prefixEnd_1546608 : Nat := 4983230072969 + 3 ^ 40 * 1546608 * 2
def baseEnd_1546608 : Nat := 264717762696330040929095

theorem tailTrace_1546608 : CollatzResearch.WordTrace tailWord_1546608 prefixEnd_1546608 264717762696330040929095 := by
  unfold tailWord_1546608
  simp only [CollatzResearch.WordTrace]
  refine ⟨28204713990455415231140239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37606285320607220308186985 28204713990455415231140239)
  ·
    refine ⟨42307070985683122846710359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28204713990455415231140239 42307070985683122846710359)
    ·
      refine ⟨63460606478524684270065539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42307070985683122846710359 63460606478524684270065539)
      ·
        refine ⟨95190909717787026405098309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63460606478524684270065539 95190909717787026405098309)
        ·
          refine ⟨17848295572085067450955933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95190909717787026405098309 17848295572085067450955933)
          ·
            refine ⟨6693110839531900294108475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17848295572085067450955933 6693110839531900294108475)
            ·
              refine ⟨10039666259297850441162713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6693110839531900294108475 10039666259297850441162713)
              ·
                refine ⟨7529749694473387830872035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10039666259297850441162713 7529749694473387830872035)
                ·
                  refine ⟨11294624541710081746308053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7529749694473387830872035 11294624541710081746308053)
                  ·
                    refine ⟨264717762696330040929095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11294624541710081746308053 264717762696330040929095)
                    ·
                      rfl

theorem cell23_1546608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 1, 7].length) (baseStart_1546608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1546608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1546608 prefixEnd_1546608 := by exact prefixLift 1546608
  have htrace : WordTrace (prefixWord ++ tailWord_1546608) baseStart_1546608 baseEnd_1546608 := by
    simpa [prefixWord, tailWord_1546608, baseEnd_1546608] using wordTrace_append hprefix tailTrace_1546608
  have hstable : (prefixWord ++ tailWord_1546608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546608).length < 2 ^ (prefixWord ++ tailWord_1546608).sum := by decide
  have hdescent : baseEnd_1546608 < baseStart_1546608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546625 : List Nat := [1, 2, 4, 3, 1, 1, 2, 1, 1, 7]
def baseStart_1546625 : Nat := 118140960795 + 1546625 * 2 ^ 59
def prefixEnd_1546625 : Nat := 4983230072969 + 3 ^ 40 * 1546625 * 2
def baseEnd_1546625 : Nat := 264720672420038852091569

theorem tailTrace_1546625 : CollatzResearch.WordTrace tailWord_1546625 prefixEnd_1546625 264720672420038852091569 := by
  unfold tailWord_1546625
  simp only [CollatzResearch.WordTrace]
  refine ⟨56410048021849242365649329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37606698681232828243766219 56410048021849242365649329)
  ·
    refine ⟨42307536016386931774236997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56410048021849242365649329 42307536016386931774236997)
    ·
      refine ⟨7932663003072549707669437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42307536016386931774236997 7932663003072549707669437)
      ·
        refine ⟨2974748626152206140376039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7932663003072549707669437 2974748626152206140376039)
        ·
          refine ⟨4462122939228309210564059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2974748626152206140376039 4462122939228309210564059)
          ·
            refine ⟨6693184408842463815846089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4462122939228309210564059 6693184408842463815846089)
            ·
              refine ⟨5019888306631847861884567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6693184408842463815846089 5019888306631847861884567)
              ·
                refine ⟨7529832459947771792826851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5019888306631847861884567 7529832459947771792826851)
                ·
                  refine ⟨11294748689921657689240277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7529832459947771792826851 11294748689921657689240277)
                  ·
                    refine ⟨264720672420038852091569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11294748689921657689240277 264720672420038852091569)
                    ·
                      rfl

theorem cell23_1546625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_1546625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1546625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1546625 prefixEnd_1546625 := by exact prefixLift 1546625
  have htrace : WordTrace (prefixWord ++ tailWord_1546625) baseStart_1546625 baseEnd_1546625 := by
    simpa [prefixWord, tailWord_1546625, baseEnd_1546625] using wordTrace_append hprefix tailTrace_1546625
  have hstable : (prefixWord ++ tailWord_1546625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546625).length < 2 ^ (prefixWord ++ tailWord_1546625).sum := by decide
  have hdescent : baseEnd_1546625 < baseStart_1546625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546676 : List Nat := [2, 5, 2, 2, 1, 1, 2, 1, 2, 5]
def baseStart_1546676 : Nat := 118140960795 + 1546676 * 2 ^ 59
def prefixEnd_1546676 : Nat := 4983230072969 + 3 ^ 40 * 1546676 * 2
def baseEnd_1546676 : Nat := 264729401591165285578991

theorem tailTrace_1546676 : CollatzResearch.WordTrace tailWord_1546676 prefixEnd_1546676 264729401591165285578991 := by
  unfold tailWord_1546676
  simp only [CollatzResearch.WordTrace]
  refine ⟨28205954072332239037877941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37607938763109652050503921 28205954072332239037877941)
  ·
    refine ⟨2644308194281147409801057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28205954072332239037877941 2644308194281147409801057)
    ·
      refine ⟨1983231145710860557350793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2644308194281147409801057 1983231145710860557350793)
      ·
        refine ⟨1487423359283145418013095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1983231145710860557350793 1487423359283145418013095)
        ·
          refine ⟨2231135038924718127019643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1487423359283145418013095 2231135038924718127019643)
          ·
            refine ⟨3346702558387077190529465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2231135038924718127019643 3346702558387077190529465)
            ·
              refine ⟨2510026918790307892897099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3346702558387077190529465 2510026918790307892897099)
              ·
                refine ⟨3765040378185461839345649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2510026918790307892897099 3765040378185461839345649)
                ·
                  refine ⟨2823780283639096379509237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3765040378185461839345649 2823780283639096379509237)
                  ·
                    refine ⟨264729401591165285578991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2823780283639096379509237 264729401591165285578991)
                    ·
                      rfl

theorem cell23_1546676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_1546676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1546676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1546676 prefixEnd_1546676 := by exact prefixLift 1546676
  have htrace : WordTrace (prefixWord ++ tailWord_1546676) baseStart_1546676 baseEnd_1546676 := by
    simpa [prefixWord, tailWord_1546676, baseEnd_1546676] using wordTrace_append hprefix tailTrace_1546676
  have hstable : (prefixWord ++ tailWord_1546676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546676).length < 2 ^ (prefixWord ++ tailWord_1546676).sum := by decide
  have hdescent : baseEnd_1546676 < baseStart_1546676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546688 : List Nat := [2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 8]
def baseStart_1546688 : Nat := 118140960795 + 1546688 * 2 ^ 59
def prefixEnd_1546688 : Nat := 4983230072969 + 3 ^ 40 * 1546688 * 2
def baseEnd_1546688 : Nat := 794194366541349809786917

theorem tailTrace_1546688 : CollatzResearch.WordTrace tailWord_1546688 prefixEnd_1546688 794194366541349809786917 := by
  unfold tailWord_1546688
  simp only [CollatzResearch.WordTrace]
  refine ⟨28206172910310502062596359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37608230547080669416795145 28206172910310502062596359)
  ·
    refine ⟨42309259365465753093894539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28206172910310502062596359 42309259365465753093894539)
    ·
      refine ⟨63463889048198629640841809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42309259365465753093894539 63463889048198629640841809)
      ·
        refine ⟨47597916786148972230631357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63463889048198629640841809 47597916786148972230631357)
        ·
          refine ⟨17849218794805864586486759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47597916786148972230631357 17849218794805864586486759)
          ·
            refine ⟨26773828192208796879730139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17849218794805864586486759 26773828192208796879730139)
            ·
              refine ⟨40160742288313195319595209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26773828192208796879730139 40160742288313195319595209)
              ·
                refine ⟨30120556716234896489696407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40160742288313195319595209 30120556716234896489696407)
                ·
                  refine ⟨45180835074352344734544611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30120556716234896489696407 45180835074352344734544611)
                  ·
                    refine ⟨67771252611528517101816917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45180835074352344734544611 67771252611528517101816917)
                    ·
                      refine ⟨794194366541349809786917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 67771252611528517101816917 794194366541349809786917)
                      ·
                        rfl

theorem cell23_1546688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 8].length) (baseStart_1546688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1546688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1546688 prefixEnd_1546688 := by exact prefixLift 1546688
  have htrace : WordTrace (prefixWord ++ tailWord_1546688) baseStart_1546688 baseEnd_1546688 := by
    simpa [prefixWord, tailWord_1546688, baseEnd_1546688] using wordTrace_append hprefix tailTrace_1546688
  have hstable : (prefixWord ++ tailWord_1546688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546688).length < 2 ^ (prefixWord ++ tailWord_1546688).sum := by decide
  have hdescent : baseEnd_1546688 < baseStart_1546688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546712 : List Nat := [2, 1, 2, 2, 2, 1, 1, 5, 3, 1, 3]
def baseStart_1546712 : Nat := 118140960795 + 1546712 * 2 ^ 59
def prefixEnd_1546712 : Nat := 4983230072969 + 3 ^ 40 * 1546712 * 2
def baseEnd_1546712 : Nat := 794206690077057715886807

theorem tailTrace_1546712 : CollatzResearch.WordTrace tailWord_1546712 prefixEnd_1546712 794206690077057715886807 := by
  unfold tailWord_1546712
  simp only [CollatzResearch.WordTrace]
  refine ⟨28206610586267028112033195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37608814115022704149377593 28206610586267028112033195)
  ·
    refine ⟨42309915879400542168049793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28206610586267028112033195 42309915879400542168049793)
    ·
      refine ⟨31732436909550406626037345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42309915879400542168049793 31732436909550406626037345)
      ·
        refine ⟨23799327682162804969528009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31732436909550406626037345 23799327682162804969528009)
        ·
          refine ⟨17849495761622103727146007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23799327682162804969528009 17849495761622103727146007)
          ·
            refine ⟨26774243642433155590719011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17849495761622103727146007 26774243642433155590719011)
            ·
              refine ⟨40161365463649733386078517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26774243642433155590719011 40161365463649733386078517)
              ·
                refine ⟨3765128012217162504944861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40161365463649733386078517 3765128012217162504944861)
                ·
                  refine ⟨1411923004581435939354323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3765128012217162504944861 1411923004581435939354323)
                  ·
                    refine ⟨2117884506872153909031485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1411923004581435939354323 2117884506872153909031485)
                    ·
                      refine ⟨794206690077057715886807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2117884506872153909031485 794206690077057715886807)
                      ·
                        rfl

theorem cell23_1546712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5, 3, 1, 3].length) (baseStart_1546712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1546712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1546712 prefixEnd_1546712 := by exact prefixLift 1546712
  have htrace : WordTrace (prefixWord ++ tailWord_1546712) baseStart_1546712 baseEnd_1546712 := by
    simpa [prefixWord, tailWord_1546712, baseEnd_1546712] using wordTrace_append hprefix tailTrace_1546712
  have hstable : (prefixWord ++ tailWord_1546712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546712).length < 2 ^ (prefixWord ++ tailWord_1546712).sum := by decide
  have hdescent : baseEnd_1546712 < baseStart_1546712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546745 : List Nat := [1, 2, 1, 3, 1, 2, 4, 2, 1, 6]
def baseStart_1546745 : Nat := 118140960795 + 1546745 * 2 ^ 59
def prefixEnd_1546745 : Nat := 4983230072969 + 3 ^ 40 * 1546745 * 2
def baseEnd_1546745 : Nat := 264741211646218695591385

theorem tailTrace_1546745 : CollatzResearch.WordTrace tailWord_1546745 prefixEnd_1546745 264741211646218695591385 := by
  unfold tailWord_1546745
  simp only [CollatzResearch.WordTrace]
  refine ⟨56414424781414502860017689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37609616520943001906678459 56414424781414502860017689)
  ·
    refine ⟨42310818586060877145013267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56414424781414502860017689 42310818586060877145013267)
    ·
      refine ⟨63466227879091315717519901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42310818586060877145013267 63466227879091315717519901)
      ·
        refine ⟨23799835454659243394069963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63466227879091315717519901 23799835454659243394069963)
        ·
          refine ⟨35699753181988865091104945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23799835454659243394069963 35699753181988865091104945)
          ·
            refine ⟨26774814886491648818328709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35699753181988865091104945 26774814886491648818328709)
            ·
              refine ⟨5020277791217184153436633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26774814886491648818328709 5020277791217184153436633)
              ·
                refine ⟨3765208343412888115077475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5020277791217184153436633 3765208343412888115077475)
                ·
                  refine ⟨5647812515119332172616213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3765208343412888115077475 5647812515119332172616213)
                  ·
                    refine ⟨264741211646218695591385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5647812515119332172616213 264741211646218695591385)
                    ·
                      rfl

theorem cell23_1546745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 2, 1, 6].length) (baseStart_1546745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1546745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1546745 prefixEnd_1546745 := by exact prefixLift 1546745
  have htrace : WordTrace (prefixWord ++ tailWord_1546745) baseStart_1546745 baseEnd_1546745 := by
    simpa [prefixWord, tailWord_1546745, baseEnd_1546745] using wordTrace_append hprefix tailTrace_1546745
  have hstable : (prefixWord ++ tailWord_1546745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546745).length < 2 ^ (prefixWord ++ tailWord_1546745).sum := by decide
  have hdescent : baseEnd_1546745 < baseStart_1546745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546755 : List Nat := [1, 1, 1, 3, 2, 1, 4, 3, 1, 1, 5]
def baseStart_1546755 : Nat := 118140960795 + 1546755 * 2 ^ 59
def prefixEnd_1546755 : Nat := 4983230072969 + 3 ^ 40 * 1546755 * 2
def baseEnd_1546755 : Nat := 794228769745201047649109

theorem tailTrace_1546755 : CollatzResearch.WordTrace tailWord_1546755 prefixEnd_1546755 794228769745201047649109 := by
  unfold tailWord_1546755
  simp only [CollatzResearch.WordTrace]
  refine ⟨56414789511378274567881719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37609859674252183045254479 56414789511378274567881719)
  ·
    refine ⟨84622184267067411851822579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56414789511378274567881719 84622184267067411851822579)
    ·
      refine ⟨126933276400601117777733869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84622184267067411851822579 126933276400601117777733869)
      ·
        refine ⟨47599978650225419166650201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126933276400601117777733869 47599978650225419166650201)
        ·
          refine ⟨35699983987669064374987651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47599978650225419166650201 35699983987669064374987651)
          ·
            refine ⟨53549975981503596562481477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35699983987669064374987651 53549975981503596562481477)
            ·
              refine ⟨10040620496531924355465277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53549975981503596562481477 10040620496531924355465277)
              ·
                refine ⟨3765232686199471633299479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10040620496531924355465277 3765232686199471633299479)
                ·
                  refine ⟨5647849029299207449949219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3765232686199471633299479 5647849029299207449949219)
                  ·
                    refine ⟨8471773543948811174923829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5647849029299207449949219 8471773543948811174923829)
                    ·
                      refine ⟨794228769745201047649109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8471773543948811174923829 794228769745201047649109)
                      ·
                        rfl

theorem cell23_1546755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3, 1, 1, 5].length) (baseStart_1546755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1546755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1546755 prefixEnd_1546755 := by exact prefixLift 1546755
  have htrace : WordTrace (prefixWord ++ tailWord_1546755) baseStart_1546755 baseEnd_1546755 := by
    simpa [prefixWord, tailWord_1546755, baseEnd_1546755] using wordTrace_append hprefix tailTrace_1546755
  have hstable : (prefixWord ++ tailWord_1546755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546755).length < 2 ^ (prefixWord ++ tailWord_1546755).sum := by decide
  have hdescent : baseEnd_1546755 < baseStart_1546755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546762 : List Nat := [3, 1, 2, 2, 2, 1, 3, 1, 4, 4]
def baseStart_1546762 : Nat := 118140960795 + 1546762 * 2 ^ 59
def prefixEnd_1546762 : Nat := 4983230072969 + 3 ^ 40 * 1546762 * 2
def baseEnd_1546762 : Nat := 264744121369927506753859

theorem tailTrace_1546762 : CollatzResearch.WordTrace tailWord_1546762 prefixEnd_1546762 264744121369927506753859 := by
  unfold tailWord_1546762
  simp only [CollatzResearch.WordTrace]
  refine ⟨14103761205588228690846635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37610029881568609842257693 14103761205588228690846635)
  ·
    refine ⟨21155641808382343036269953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14103761205588228690846635 21155641808382343036269953)
    ·
      refine ⟨15866731356286757277202465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21155641808382343036269953 15866731356286757277202465)
      ·
        refine ⟨11900048517215067957901849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15866731356286757277202465 11900048517215067957901849)
        ·
          refine ⟨8925036387911300968426387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11900048517215067957901849 8925036387911300968426387)
          ·
            refine ⟨13387554581866951452639581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8925036387911300968426387 13387554581866951452639581)
            ·
              refine ⟨5020332968200106794739843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13387554581866951452639581 5020332968200106794739843)
              ·
                refine ⟨7530499452300160192109765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5020332968200106794739843 7530499452300160192109765)
                ·
                  refine ⟨1411968647306280036020581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7530499452300160192109765 1411968647306280036020581)
                  ·
                    refine ⟨264744121369927506753859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1411968647306280036020581 264744121369927506753859)
                    ·
                      rfl

theorem cell23_1546762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 4, 4].length) (baseStart_1546762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1546762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1546762 prefixEnd_1546762 := by exact prefixLift 1546762
  have htrace : WordTrace (prefixWord ++ tailWord_1546762) baseStart_1546762 baseEnd_1546762 := by
    simpa [prefixWord, tailWord_1546762, baseEnd_1546762] using wordTrace_append hprefix tailTrace_1546762
  have hstable : (prefixWord ++ tailWord_1546762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546762).length < 2 ^ (prefixWord ++ tailWord_1546762).sum := by decide
  have hdescent : baseEnd_1546762 < baseStart_1546762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546792 : List Nat := [2, 1, 5, 2, 1, 2, 1, 9]
def baseStart_1546792 : Nat := 118140960795 + 1546792 * 2 ^ 59
def prefixEnd_1546792 : Nat := 4983230072969 + 3 ^ 40 * 1546792 * 2
def baseEnd_1546792 : Nat := 29416584019608051958757

theorem tailTrace_1546792 : CollatzResearch.WordTrace tailWord_1546792 prefixEnd_1546792 29416584019608051958757 := by
  unfold tailWord_1546792
  simp only [CollatzResearch.WordTrace]
  refine ⟨28208069506122114943489315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37610759341496153257985753 28208069506122114943489315)
  ·
    refine ⟨42312104259183172415233973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28208069506122114943489315 42312104259183172415233973)
    ·
      refine ⟨3966759774298422413928185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42312104259183172415233973 3966759774298422413928185)
      ·
        refine ⟨2975069830723816810446139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3966759774298422413928185 2975069830723816810446139)
        ·
          refine ⟨4462604746085725215669209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2975069830723816810446139 4462604746085725215669209)
          ·
            refine ⟨3346953559564293911751907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4462604746085725215669209 3346953559564293911751907)
            ·
              refine ⟨5020430339346440867627861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3346953559564293911751907 5020430339346440867627861)
              ·
                refine ⟨29416584019608051958757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5020430339346440867627861 29416584019608051958757)
                ·
                  rfl

theorem cell23_1546792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 9].length) (baseStart_1546792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1546792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1546792 prefixEnd_1546792 := by exact prefixLift 1546792
  have htrace : WordTrace (prefixWord ++ tailWord_1546792) baseStart_1546792 baseEnd_1546792 := by
    simpa [prefixWord, tailWord_1546792, baseEnd_1546792] using wordTrace_append hprefix tailTrace_1546792
  have hstable : (prefixWord ++ tailWord_1546792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546792).length < 2 ^ (prefixWord ++ tailWord_1546792).sum := by decide
  have hdescent : baseEnd_1546792 < baseStart_1546792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546802 : List Nat := [3, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3]
def baseStart_1546802 : Nat := 118140960795 + 1546802 * 2 ^ 59
def prefixEnd_1546802 : Nat := 4983230072969 + 3 ^ 40 * 1546802 * 2
def baseEnd_1546802 : Nat := 794252903335962363761393

theorem tailTrace_1546802 : CollatzResearch.WordTrace tailWord_1546802 prefixEnd_1546802 794252903335962363761393 := by
  unfold tailWord_1546802
  simp only [CollatzResearch.WordTrace]
  refine ⟨14104125935552000398710665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37611002494805334396561773 14104125935552000398710665)
  ·
    refine ⟨10578094451664000299032999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14104125935552000398710665 10578094451664000299032999)
    ·
      refine ⟨15867141677496000448549499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10578094451664000299032999 15867141677496000448549499)
      ·
        refine ⟨23800712516244000672824249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15867141677496000448549499 23800712516244000672824249)
        ·
          refine ⟨17850534387183000504618187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23800712516244000672824249 17850534387183000504618187)
          ·
            refine ⟨26775801580774500756927281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17850534387183000504618187 26775801580774500756927281)
            ·
              refine ⟨20081851185580875567695461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26775801580774500756927281 20081851185580875567695461)
              ·
                refine ⟨3765347097296414168942899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20081851185580875567695461 3765347097296414168942899)
                ·
                  refine ⟨5648020645944621253414349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3765347097296414168942899 5648020645944621253414349)
                  ·
                    refine ⟨2118007742229232970030381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5648020645944621253414349 2118007742229232970030381)
                    ·
                      refine ⟨794252903335962363761393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2118007742229232970030381 794252903335962363761393)
                      ·
                        rfl

theorem cell23_1546802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3].length) (baseStart_1546802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1546802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1546802 prefixEnd_1546802 := by exact prefixLift 1546802
  have htrace : WordTrace (prefixWord ++ tailWord_1546802) baseStart_1546802 baseEnd_1546802 := by
    simpa [prefixWord, tailWord_1546802, baseEnd_1546802] using wordTrace_append hprefix tailTrace_1546802
  have hstable : (prefixWord ++ tailWord_1546802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546802).length < 2 ^ (prefixWord ++ tailWord_1546802).sum := by decide
  have hdescent : baseEnd_1546802 < baseStart_1546802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546806 : List Nat := [5, 1, 2, 1, 2, 1, 2, 3, 1, 2, 3]
def baseStart_1546806 : Nat := 118140960795 + 1546806 * 2 ^ 59
def prefixEnd_1546806 : Nat := 4983230072969 + 3 ^ 40 * 1546806 * 2
def baseEnd_1546806 : Nat := 794254957258580348111375

theorem tailTrace_1546806 : CollatzResearch.WordTrace tailWord_1546806 prefixEnd_1546806 794254957258580348111375 := by
  unfold tailWord_1546806
  simp only [CollatzResearch.WordTrace]
  refine ⟨3526040602137094392374267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37611099756129006851992181 3526040602137094392374267)
  ·
    refine ⟨5289060903205641588561401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3526040602137094392374267 5289060903205641588561401)
    ·
      refine ⟨3966795677404231191421051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5289060903205641588561401 3966795677404231191421051)
      ·
        refine ⟨5950193516106346787131577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3966795677404231191421051 5950193516106346787131577)
        ·
          refine ⟨4462645137079760090348683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5950193516106346787131577 4462645137079760090348683)
          ·
            refine ⟨6693967705619640135523025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4462645137079760090348683 6693967705619640135523025)
            ·
              refine ⟨5020475779214730101642269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6693967705619640135523025 5020475779214730101642269)
              ·
                refine ⟨1882678417205523788115851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5020475779214730101642269 1882678417205523788115851)
                ·
                  refine ⟨2824017625808285682173777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1882678417205523788115851 2824017625808285682173777)
                  ·
                    refine ⟨2118013219356214261630333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2824017625808285682173777 2118013219356214261630333)
                    ·
                      refine ⟨794254957258580348111375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2118013219356214261630333 794254957258580348111375)
                      ·
                        rfl

theorem cell23_1546806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_1546806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1546806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1546806 prefixEnd_1546806 := by exact prefixLift 1546806
  have htrace : WordTrace (prefixWord ++ tailWord_1546806) baseStart_1546806 baseEnd_1546806 := by
    simpa [prefixWord, tailWord_1546806, baseEnd_1546806] using wordTrace_append hprefix tailTrace_1546806
  have hstable : (prefixWord ++ tailWord_1546806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546806).length < 2 ^ (prefixWord ++ tailWord_1546806).sum := by decide
  have hdescent : baseEnd_1546806 < baseStart_1546806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546815 : List Nat := [1, 1, 2, 2, 3, 2, 1, 2, 2, 2, 5]
def baseStart_1546815 : Nat := 118140960795 + 1546815 * 2 ^ 59
def prefixEnd_1546815 : Nat := 4983230072969 + 3 ^ 40 * 1546815 * 2
def baseEnd_1546815 : Nat := 794259578584470812898833

theorem tailTrace_1546815 : CollatzResearch.WordTrace tailWord_1546815 prefixEnd_1546815 794259578584470812898833 := by
  unfold tailWord_1546815
  simp only [CollatzResearch.WordTrace]
  refine ⟨56416977891160904815065899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37611318594107269876710599 56416977891160904815065899)
  ·
    refine ⟨84625466836741357222598849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56416977891160904815065899 84625466836741357222598849)
    ·
      refine ⟨63469100127556017916949137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84625466836741357222598849 63469100127556017916949137)
      ·
        refine ⟨47601825095667013437711853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63469100127556017916949137 47601825095667013437711853)
        ·
          refine ⟨17850684410875130039141945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47601825095667013437711853 17850684410875130039141945)
          ·
            refine ⟨13388013308156347529356459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17850684410875130039141945 13388013308156347529356459)
            ·
              refine ⟨20082019962234521294034689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13388013308156347529356459 20082019962234521294034689)
              ·
                refine ⟨15061514971675890970526017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20082019962234521294034689 15061514971675890970526017)
                ·
                  refine ⟨11296136228756918227894513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15061514971675890970526017 11296136228756918227894513)
                  ·
                    refine ⟨8472102171567688670920885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11296136228756918227894513 8472102171567688670920885)
                    ·
                      refine ⟨794259578584470812898833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8472102171567688670920885 794259578584470812898833)
                      ·
                        rfl

theorem cell23_1546815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 2, 5].length) (baseStart_1546815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1546815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1546815 prefixEnd_1546815 := by exact prefixLift 1546815
  have htrace : WordTrace (prefixWord ++ tailWord_1546815) baseStart_1546815 baseEnd_1546815 := by
    simpa [prefixWord, tailWord_1546815, baseEnd_1546815] using wordTrace_append hprefix tailTrace_1546815
  have hstable : (prefixWord ++ tailWord_1546815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546815).length < 2 ^ (prefixWord ++ tailWord_1546815).sum := by decide
  have hdescent : baseEnd_1546815 < baseStart_1546815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546836 : List Nat := [2, 4, 1, 1, 1, 4, 1, 3, 2, 1, 3]
def baseStart_1546836 : Nat := 118140960795 + 1546836 * 2 ^ 59
def prefixEnd_1546836 : Nat := 4983230072969 + 3 ^ 40 * 1546836 * 2
def baseEnd_1546836 : Nat := 794270361678215230736237

theorem tailTrace_1546836 : CollatzResearch.WordTrace tailWord_1546836 prefixEnd_1546836 794270361678215230736237 := by
  unfold tailWord_1546836
  simp only [CollatzResearch.WordTrace]
  refine ⟨28208871912042412700790181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37611829216056550267720241 28208871912042412700790181)
  ·
    refine ⟨5289163483507952381398159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28208871912042412700790181 5289163483507952381398159)
    ·
      refine ⟨7933745225261928572097239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5289163483507952381398159 7933745225261928572097239)
      ·
        refine ⟨11900617837892892858145859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7933745225261928572097239 11900617837892892858145859)
        ·
          refine ⟨17850926756839339287218789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11900617837892892858145859 17850926756839339287218789)
          ·
            refine ⟨3347048766907376116353523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17850926756839339287218789 3347048766907376116353523)
            ·
              refine ⟨5020573150361064174530285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3347048766907376116353523 5020573150361064174530285)
              ·
                refine ⟨1882714931385399065448857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5020573150361064174530285 1882714931385399065448857)
                ·
                  refine ⟨1412036198539049299086643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1882714931385399065448857 1412036198539049299086643)
                  ·
                    refine ⟨2118054297808573948629965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1412036198539049299086643 2118054297808573948629965)
                    ·
                      refine ⟨794270361678215230736237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2118054297808573948629965 794270361678215230736237)
                      ·
                        rfl

theorem cell23_1546836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 3, 2, 1, 3].length) (baseStart_1546836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1546836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1546836 prefixEnd_1546836 := by exact prefixLift 1546836
  have htrace : WordTrace (prefixWord ++ tailWord_1546836) baseStart_1546836 baseEnd_1546836 := by
    simpa [prefixWord, tailWord_1546836, baseEnd_1546836] using wordTrace_append hprefix tailTrace_1546836
  have hstable : (prefixWord ++ tailWord_1546836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546836).length < 2 ^ (prefixWord ++ tailWord_1546836).sum := by decide
  have hdescent : baseEnd_1546836 < baseStart_1546836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546859 : List Nat := [1, 1, 1, 1, 2, 2, 1, 6, 4, 2, 2]
def baseStart_1546859 : Nat := 118140960795 + 1546859 * 2 ^ 59
def prefixEnd_1546859 : Nat := 4983230072969 + 3 ^ 40 * 1546859 * 2
def baseEnd_1546859 : Nat := 794282171733268640748631

theorem tailTrace_1546859 : CollatzResearch.WordTrace tailWord_1546859 prefixEnd_1546859 794282171733268640748631 := by
  unfold tailWord_1546859
  simp only [CollatzResearch.WordTrace]
  refine ⟨56418582703001500329667631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37612388468667666886445087 56418582703001500329667631)
  ·
    refine ⟨84627874054502250494501447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56418582703001500329667631 84627874054502250494501447)
    ·
      refine ⟨126941811081753375741752171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84627874054502250494501447 126941811081753375741752171)
      ·
        refine ⟨190412716622630063612628257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126941811081753375741752171 190412716622630063612628257)
        ·
          refine ⟨142809537466972547709471193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190412716622630063612628257 142809537466972547709471193)
          ·
            refine ⟨107107153100229410782103395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142809537466972547709471193 107107153100229410782103395)
            ·
              refine ⟨160660729650344116173155093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107107153100229410782103395 160660729650344116173155093)
              ·
                refine ⟨7530971702359880445616645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 160660729650344116173155093 7530971702359880445616645)
                ·
                  refine ⟨1412057194192477583553121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7530971702359880445616645 1412057194192477583553121)
                  ·
                    refine ⟨1059042895644358187664841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1412057194192477583553121 1059042895644358187664841)
                    ·
                      refine ⟨794282171733268640748631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1059042895644358187664841 794282171733268640748631)
                      ·
                        rfl

theorem cell23_1546859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 4, 2, 2].length) (baseStart_1546859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1546859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1546859 prefixEnd_1546859 := by exact prefixLift 1546859
  have htrace : WordTrace (prefixWord ++ tailWord_1546859) baseStart_1546859 baseEnd_1546859 := by
    simpa [prefixWord, tailWord_1546859, baseEnd_1546859] using wordTrace_append hprefix tailTrace_1546859
  have hstable : (prefixWord ++ tailWord_1546859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546859).length < 2 ^ (prefixWord ++ tailWord_1546859).sum := by decide
  have hdescent : baseEnd_1546859 < baseStart_1546859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546876 : List Nat := [2, 2, 2, 1, 1, 2, 3, 4, 2, 2, 2]
def baseStart_1546876 : Nat := 118140960795 + 1546876 * 2 ^ 59
def prefixEnd_1546876 : Nat := 4983230072969 + 3 ^ 40 * 1546876 * 2
def baseEnd_1546876 : Nat := 794290900904395074236053

theorem tailTrace_1546876 : CollatzResearch.WordTrace tailWord_1546876 prefixEnd_1546876 794290900904395074236053 := by
  unfold tailWord_1546876
  simp only [CollatzResearch.WordTrace]
  refine ⟨28209601371969956116518241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37612801829293274822024321 28209601371969956116518241)
  ·
    refine ⟨21157201028977467087388681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28209601371969956116518241 21157201028977467087388681)
    ·
      refine ⟨15867900771733100315541511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21157201028977467087388681 15867900771733100315541511)
      ·
        refine ⟨23801851157599650473312267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15867900771733100315541511 23801851157599650473312267)
        ·
          refine ⟨35702776736399475709968401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23801851157599650473312267 35702776736399475709968401)
          ·
            refine ⟨26777082552299606782476301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35702776736399475709968401 26777082552299606782476301)
            ·
              refine ⟨10041405957112352543428613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26777082552299606782476301 10041405957112352543428613)
              ·
                refine ⟨1882763616958566101892865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10041405957112352543428613 1882763616958566101892865)
                ·
                  refine ⟨1412072712718924576419649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1882763616958566101892865 1412072712718924576419649)
                  ·
                    refine ⟨1059054534539193432314737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1412072712718924576419649 1059054534539193432314737)
                    ·
                      refine ⟨794290900904395074236053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1059054534539193432314737 794290900904395074236053)
                      ·
                        rfl

theorem cell23_1546876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 4, 2, 2, 2].length) (baseStart_1546876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1546876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1546876 prefixEnd_1546876 := by exact prefixLift 1546876
  have htrace : WordTrace (prefixWord ++ tailWord_1546876) baseStart_1546876 baseEnd_1546876 := by
    simpa [prefixWord, tailWord_1546876, baseEnd_1546876] using wordTrace_append hprefix tailTrace_1546876
  have hstable : (prefixWord ++ tailWord_1546876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546876).length < 2 ^ (prefixWord ++ tailWord_1546876).sum := by decide
  have hdescent : baseEnd_1546876 < baseStart_1546876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546895 : List Nat := [1, 1, 2, 1, 1, 1, 1, 5, 3, 7]
def baseStart_1546895 : Nat := 118140960795 + 1546895 * 2 ^ 59
def prefixEnd_1546895 : Nat := 4983230072969 + 3 ^ 40 * 1546895 * 2
def baseEnd_1546895 : Nat := 264766885678943499966155

theorem tailTrace_1546895 : CollatzResearch.WordTrace tailWord_1546895 prefixEnd_1546895 264766885678943499966155 := by
  unfold tailWord_1546895
  simp only [CollatzResearch.WordTrace]
  refine ⟨56419895730871078477978139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37613263820580718985318759 56419895730871078477978139)
  ·
    refine ⟨84629843596306617716967209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56419895730871078477978139 84629843596306617716967209)
    ·
      refine ⟨63472382697229963287725407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84629843596306617716967209 63472382697229963287725407)
      ·
        refine ⟨95208574045844944931588111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63472382697229963287725407 95208574045844944931588111)
        ·
          refine ⟨142812861068767417397382167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95208574045844944931588111 142812861068767417397382167)
          ·
            refine ⟨214219291603151126096073251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142812861068767417397382167 214219291603151126096073251)
            ·
              refine ⟨321328937404726689144109877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214219291603151126096073251 321328937404726689144109877)
              ·
                refine ⟨30124587881693127107260301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 321328937404726689144109877 30124587881693127107260301)
                ·
                  refine ⟨11296720455634922665222613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30124587881693127107260301 11296720455634922665222613)
                  ·
                    refine ⟨264766885678943499966155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11296720455634922665222613 264766885678943499966155)
                    ·
                      rfl

theorem cell23_1546895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 7].length) (baseStart_1546895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1546895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1546895 prefixEnd_1546895 := by exact prefixLift 1546895
  have htrace : WordTrace (prefixWord ++ tailWord_1546895) baseStart_1546895 baseEnd_1546895 := by
    simpa [prefixWord, tailWord_1546895, baseEnd_1546895] using wordTrace_append hprefix tailTrace_1546895
  have hstable : (prefixWord ++ tailWord_1546895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546895).length < 2 ^ (prefixWord ++ tailWord_1546895).sum := by decide
  have hdescent : baseEnd_1546895 < baseStart_1546895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546926 : List Nat := [4, 1, 4, 1, 1, 1, 1, 2, 2, 3, 3]
def baseStart_1546926 : Nat := 118140960795 + 1546926 * 2 ^ 59
def prefixEnd_1546926 : Nat := 4983230072969 + 3 ^ 40 * 1546926 * 2
def baseEnd_1546926 : Nat := 794316574937119878610823

theorem tailTrace_1546926 : CollatzResearch.WordTrace tailWord_1546926 prefixEnd_1546926 794316574937119878610823 := by
  unfold tailWord_1546926
  simp only [CollatzResearch.WordTrace]
  refine ⟨7052628299219846346544579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37614017595839180514904421 7052628299219846346544579)
  ·
    refine ⟨10578942448829769519816869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7052628299219846346544579 10578942448829769519816869)
    ·
      refine ⟨1983551709155581784965663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10578942448829769519816869 1983551709155581784965663)
      ·
        refine ⟨2975327563733372677448495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1983551709155581784965663 2975327563733372677448495)
        ·
          refine ⟨4462991345600059016172743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2975327563733372677448495 4462991345600059016172743)
          ·
            refine ⟨6694487018400088524259115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4462991345600059016172743 6694487018400088524259115)
            ·
              refine ⟨10041730527600132786388673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6694487018400088524259115 10041730527600132786388673)
              ·
                refine ⟨7531297895700099589791505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10041730527600132786388673 7531297895700099589791505)
                ·
                  refine ⟨5648473421775074692343629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7531297895700099589791505 5648473421775074692343629)
                  ·
                    refine ⟨2118177533165653009628861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5648473421775074692343629 2118177533165653009628861)
                    ·
                      refine ⟨794316574937119878610823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2118177533165653009628861 794316574937119878610823)
                      ·
                        rfl

theorem cell23_1546926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_1546926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1546926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1546926 prefixEnd_1546926 := by exact prefixLift 1546926
  have htrace : WordTrace (prefixWord ++ tailWord_1546926) baseStart_1546926 baseEnd_1546926 := by
    simpa [prefixWord, tailWord_1546926, baseEnd_1546926] using wordTrace_append hprefix tailTrace_1546926
  have hstable : (prefixWord ++ tailWord_1546926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546926).length < 2 ^ (prefixWord ++ tailWord_1546926).sum := by decide
  have hdescent : baseEnd_1546926 < baseStart_1546926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546969 : List Nat := [1, 2, 1, 2, 3, 2, 2, 3, 2, 2, 3]
def baseStart_1546969 : Nat := 118140960795 + 1546969 * 2 ^ 59
def prefixEnd_1546969 : Nat := 4983230072969 + 3 ^ 40 * 1546969 * 2
def baseEnd_1546969 : Nat := 794338654605263210373125

theorem tailTrace_1546969 : CollatzResearch.WordTrace tailWord_1546969 prefixEnd_1546969 794338654605263210373125 := by
  unfold tailWord_1546969
  simp only [CollatzResearch.WordTrace]
  refine ⟨56422594732602989116171961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37615063155068659410781307 56422594732602989116171961)
  ·
    refine ⟨42316946049452241837128971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56422594732602989116171961 42316946049452241837128971)
    ·
      refine ⟨63475419074178362755693457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42316946049452241837128971 63475419074178362755693457)
      ·
        refine ⟨47606564305633772066770093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63475419074178362755693457 47606564305633772066770093)
        ·
          refine ⟨17852461614612664525038785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47606564305633772066770093 17852461614612664525038785)
          ·
            refine ⟨13389346210959498393779089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17852461614612664525038785 13389346210959498393779089)
            ·
              refine ⟨10042009658219623795334317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13389346210959498393779089 10042009658219623795334317)
              ·
                refine ⟨3765753621832358923250369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10042009658219623795334317 3765753621832358923250369)
                ·
                  refine ⟨2824315216374269192437777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3765753621832358923250369 2824315216374269192437777)
                  ·
                    refine ⟨2118236412280701894328333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2824315216374269192437777 2118236412280701894328333)
                    ·
                      refine ⟨794338654605263210373125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2118236412280701894328333 794338654605263210373125)
                      ·
                        rfl

theorem cell23_1546969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3, 2, 2, 3].length) (baseStart_1546969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1546969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1546969 prefixEnd_1546969 := by exact prefixLift 1546969
  have htrace : WordTrace (prefixWord ++ tailWord_1546969) baseStart_1546969 baseEnd_1546969 := by
    simpa [prefixWord, tailWord_1546969, baseEnd_1546969] using wordTrace_append hprefix tailTrace_1546969
  have hstable : (prefixWord ++ tailWord_1546969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546969).length < 2 ^ (prefixWord ++ tailWord_1546969).sum := by decide
  have hdescent : baseEnd_1546969 < baseStart_1546969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546989 : List Nat := [1, 5, 1, 2, 1, 1, 2, 4, 6]
def baseStart_1546989 : Nat := 118140960795 + 1546989 * 2 ^ 59
def prefixEnd_1546989 : Nat := 4983230072969 + 3 ^ 40 * 1546989 * 2
def baseEnd_1546989 : Nat := 88260991579817014680337

theorem tailTrace_1546989 : CollatzResearch.WordTrace tailWord_1546989 prefixEnd_1546989 88260991579817014680337 := by
  unfold tailWord_1546989
  simp only [CollatzResearch.WordTrace]
  refine ⟨56423324192530532531900021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37615549461687021687933347 56423324192530532531900021)
  ·
    refine ⟨5289686643049737424865627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56423324192530532531900021 5289686643049737424865627)
    ·
      refine ⟨7934529964574606137298441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5289686643049737424865627 7934529964574606137298441)
      ·
        refine ⟨5950897473430954602973831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7934529964574606137298441 5950897473430954602973831)
        ·
          refine ⟨8926346210146431904460747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5950897473430954602973831 8926346210146431904460747)
          ·
            refine ⟨13389519315219647856691121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8926346210146431904460747 13389519315219647856691121)
            ·
              refine ⟨10042139486414735892518341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13389519315219647856691121 10042139486414735892518341)
              ·
                refine ⟨1882901153702762979847189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10042139486414735892518341 1882901153702762979847189)
                ·
                  refine ⟨88260991579817014680337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1882901153702762979847189 88260991579817014680337)
                  ·
                    rfl

theorem cell23_1546989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 4, 6].length) (baseStart_1546989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1546989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1546989 prefixEnd_1546989 := by exact prefixLift 1546989
  have htrace : WordTrace (prefixWord ++ tailWord_1546989) baseStart_1546989 baseEnd_1546989 := by
    simpa [prefixWord, tailWord_1546989, baseEnd_1546989] using wordTrace_append hprefix tailTrace_1546989
  have hstable : (prefixWord ++ tailWord_1546989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546989).length < 2 ^ (prefixWord ++ tailWord_1546989).sum := by decide
  have hdescent : baseEnd_1546989 < baseStart_1546989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546993 : List Nat := [1, 2, 2, 2, 2, 2, 5, 2, 1, 4]
def baseStart_1546993 : Nat := 118140960795 + 1546993 * 2 ^ 59
def prefixEnd_1546993 : Nat := 4983230072969 + 3 ^ 40 * 1546993 * 2
def baseEnd_1546993 : Nat := 264783659380323705491005

theorem tailTrace_1546993 : CollatzResearch.WordTrace tailWord_1546993 prefixEnd_1546993 264783659380323705491005 := by
  unfold tailWord_1546993
  simp only [CollatzResearch.WordTrace]
  refine ⟨56423470084516041215045633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37615646723010694143363755 56423470084516041215045633)
  ·
    refine ⟨42317602563387030911284225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56423470084516041215045633 42317602563387030911284225)
    ·
      refine ⟨31738201922540273183463169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42317602563387030911284225 31738201922540273183463169)
      ·
        refine ⟨23803651441905204887597377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31738201922540273183463169 23803651441905204887597377)
        ·
          refine ⟨17852738581428903665698033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23803651441905204887597377 17852738581428903665698033)
          ·
            refine ⟨13389553936071677749273525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17852738581428903665698033 13389553936071677749273525)
            ·
              refine ⟨1255270681506719788994393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13389553936071677749273525 1255270681506719788994393)
              ·
                refine ⟨941453011130039841745795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1255270681506719788994393 941453011130039841745795)
                ·
                  refine ⟨1412179516695059762618693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 941453011130039841745795 1412179516695059762618693)
                  ·
                    refine ⟨264783659380323705491005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1412179516695059762618693 264783659380323705491005)
                    ·
                      rfl

theorem cell23_1546993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5, 2, 1, 4].length) (baseStart_1546993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1546993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1546993 prefixEnd_1546993 := by exact prefixLift 1546993
  have htrace : WordTrace (prefixWord ++ tailWord_1546993) baseStart_1546993 baseEnd_1546993 := by
    simpa [prefixWord, tailWord_1546993, baseEnd_1546993] using wordTrace_append hprefix tailTrace_1546993
  have hstable : (prefixWord ++ tailWord_1546993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546993).length < 2 ^ (prefixWord ++ tailWord_1546993).sum := by decide
  have hdescent : baseEnd_1546993 < baseStart_1546993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547006 : List Nat := [4, 2, 2, 1, 2, 2, 1, 3, 6]
def baseStart_1547006 : Nat := 118140960795 + 1547006 * 2 ^ 59
def prefixEnd_1547006 : Nat := 4983230072969 + 3 ^ 40 * 1547006 * 2
def baseEnd_1547006 : Nat := 88261961487719951734495

theorem tailTrace_1547006 : CollatzResearch.WordTrace tailWord_1547006 prefixEnd_1547006 88261961487719951734495 := by
  unfold tailWord_1547006
  simp only [CollatzResearch.WordTrace]
  refine ⟨7052993029183618054408609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37615962822312629623512581 7052993029183618054408609)
  ·
    refine ⟨5289744771887713540806457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7052993029183618054408609 5289744771887713540806457)
    ·
      refine ⟨3967308578915785155604843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5289744771887713540806457 3967308578915785155604843)
      ·
        refine ⟨5950962868373677733407265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3967308578915785155604843 5950962868373677733407265)
        ·
          refine ⟨4463222151280258300055449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5950962868373677733407265 4463222151280258300055449)
          ·
            refine ⟨3347416613460193725041587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4463222151280258300055449 3347416613460193725041587)
            ·
              refine ⟨5021124920190290587562381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3347416613460193725041587 5021124920190290587562381)
              ·
                refine ⟨1882921845071358970335893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5021124920190290587562381 1882921845071358970335893)
                ·
                  refine ⟨88261961487719951734495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1882921845071358970335893 88261961487719951734495)
                  ·
                    rfl

theorem cell23_1547006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 3, 6].length) (baseStart_1547006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1547006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1547006 prefixEnd_1547006 := by exact prefixLift 1547006
  have htrace : WordTrace (prefixWord ++ tailWord_1547006) baseStart_1547006 baseEnd_1547006 := by
    simpa [prefixWord, tailWord_1547006, baseEnd_1547006] using wordTrace_append hprefix tailTrace_1547006
  have hstable : (prefixWord ++ tailWord_1547006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547006).length < 2 ^ (prefixWord ++ tailWord_1547006).sum := by decide
  have hdescent : baseEnd_1547006 < baseStart_1547006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547056 : List Nat := [2, 1, 1, 1, 2, 2, 1, 2, 7, 2, 2]
def baseStart_1547056 : Nat := 118140960795 + 1547056 * 2 ^ 59
def prefixEnd_1547056 : Nat := 4983230072969 + 3 ^ 40 * 1547056 * 2
def baseEnd_1547056 : Nat := 794383327422204369985225

theorem tailTrace_1547056 : CollatzResearch.WordTrace tailWord_1547056 prefixEnd_1547056 794383327422204369985225 := by
  unfold tailWord_1547056
  simp only [CollatzResearch.WordTrace]
  refine ⟨28212883941643901487294511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37617178588858535316392681 28212883941643901487294511)
  ·
    refine ⟨42319325912465852230941767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28212883941643901487294511 42319325912465852230941767)
    ·
      refine ⟨63478988868698778346412651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42319325912465852230941767 63478988868698778346412651)
      ·
        refine ⟨95218483303048167519618977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63478988868698778346412651 95218483303048167519618977)
        ·
          refine ⟨71413862477286125639714233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95218483303048167519618977 71413862477286125639714233)
          ·
            refine ⟨53560396857964594229785675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71413862477286125639714233 53560396857964594229785675)
            ·
              refine ⟨80340595286946891344678513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53560396857964594229785675 80340595286946891344678513)
              ·
                refine ⟨60255446465210168508508885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80340595286946891344678513 60255446465210168508508885)
                ·
                  refine ⟨1412237026528363324418177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 60255446465210168508508885 1412237026528363324418177)
                  ·
                    refine ⟨1059177769896272493313633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1412237026528363324418177 1059177769896272493313633)
                    ·
                      refine ⟨794383327422204369985225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1059177769896272493313633 794383327422204369985225)
                      ·
                        rfl

theorem cell23_1547056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 7, 2, 2].length) (baseStart_1547056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1547056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1547056 prefixEnd_1547056 := by exact prefixLift 1547056
  have htrace : WordTrace (prefixWord ++ tailWord_1547056) baseStart_1547056 baseEnd_1547056 := by
    simpa [prefixWord, tailWord_1547056, baseEnd_1547056] using wordTrace_append hprefix tailTrace_1547056
  have hstable : (prefixWord ++ tailWord_1547056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547056).length < 2 ^ (prefixWord ++ tailWord_1547056).sum := by decide
  have hdescent : baseEnd_1547056 < baseStart_1547056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547066 : List Nat := [3, 1, 1, 1, 6, 1, 2, 1, 1, 6]
def baseStart_1547066 : Nat := 118140960795 + 1547066 * 2 ^ 59
def prefixEnd_1547066 : Nat := 4983230072969 + 3 ^ 40 * 1547066 * 2
def baseEnd_1547066 : Nat := 264796154076249776953393

theorem tailTrace_1547066 : CollatzResearch.WordTrace tailWord_1547066 prefixEnd_1547066 264796154076249776953393 := by
  unfold tailWord_1547066
  simp only [CollatzResearch.WordTrace]
  refine ⟨14106533153312893670613263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37617421742167716454968701 14106533153312893670613263)
  ·
    refine ⟨21159799729969340505919895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14106533153312893670613263 21159799729969340505919895)
    ·
      refine ⟨31739699594954010758879843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21159799729969340505919895 31739699594954010758879843)
      ·
        refine ⟨47609549392431016138319765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31739699594954010758879843 47609549392431016138319765)
        ·
          refine ⟨2231697627770203881483739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 47609549392431016138319765 2231697627770203881483739)
          ·
            refine ⟨3347546441655305822225609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2231697627770203881483739 3347546441655305822225609)
            ·
              refine ⟨2510659831241479366669207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3347546441655305822225609 2510659831241479366669207)
              ·
                refine ⟨3765989746862219050003811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2510659831241479366669207 3765989746862219050003811)
                ·
                  refine ⟨5648984620293328575005717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3765989746862219050003811 5648984620293328575005717)
                  ·
                    refine ⟨264796154076249776953393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5648984620293328575005717 264796154076249776953393)
                    ·
                      rfl

theorem cell23_1547066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 1, 1, 6].length) (baseStart_1547066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1547066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1547066 prefixEnd_1547066 := by exact prefixLift 1547066
  have htrace : WordTrace (prefixWord ++ tailWord_1547066) baseStart_1547066 baseEnd_1547066 := by
    simpa [prefixWord, tailWord_1547066, baseEnd_1547066] using wordTrace_append hprefix tailTrace_1547066
  have hstable : (prefixWord ++ tailWord_1547066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547066).length < 2 ^ (prefixWord ++ tailWord_1547066).sum := by decide
  have hdescent : baseEnd_1547066 < baseStart_1547066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547072 : List Nat := [2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 7]
def baseStart_1547072 : Nat := 118140960795 + 1547072 * 2 ^ 59
def prefixEnd_1547072 : Nat := 4983230072969 + 3 ^ 40 * 1547072 * 2
def baseEnd_1547072 : Nat := 794391543112676307385151

theorem tailTrace_1547072 : CollatzResearch.WordTrace tailWord_1547072 prefixEnd_1547072 794391543112676307385151 := by
  unfold tailWord_1547072
  simp only [CollatzResearch.WordTrace]
  refine ⟨28213175725614918853585735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37617567634153225138114313 28213175725614918853585735)
  ·
    refine ⟨42319763588422378280378603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28213175725614918853585735 42319763588422378280378603)
    ·
      refine ⟨63479645382633567420567905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42319763588422378280378603 63479645382633567420567905)
      ·
        refine ⟨47609734036975175565425929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63479645382633567420567905 47609734036975175565425929)
        ·
          refine ⟨35707300527731381674069447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47609734036975175565425929 35707300527731381674069447)
          ·
            refine ⟨53560950791597072511104171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35707300527731381674069447 53560950791597072511104171)
            ·
              refine ⟨80341426187395608766656257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53560950791597072511104171 80341426187395608766656257)
              ·
                refine ⟨60256069640546706574992193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80341426187395608766656257 60256069640546706574992193)
                ·
                  refine ⟨45192052230410029931244145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60256069640546706574992193 45192052230410029931244145)
                  ·
                    refine ⟨33894039172807522448433109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45192052230410029931244145 33894039172807522448433109)
                    ·
                      refine ⟨794391543112676307385151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 33894039172807522448433109 794391543112676307385151)
                      ·
                        rfl

theorem cell23_1547072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 7].length) (baseStart_1547072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1547072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1547072 prefixEnd_1547072 := by exact prefixLift 1547072
  have htrace : WordTrace (prefixWord ++ tailWord_1547072) baseStart_1547072 baseEnd_1547072 := by
    simpa [prefixWord, tailWord_1547072, baseEnd_1547072] using wordTrace_append hprefix tailTrace_1547072
  have hstable : (prefixWord ++ tailWord_1547072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547072).length < 2 ^ (prefixWord ++ tailWord_1547072).sum := by decide
  have hdescent : baseEnd_1547072 < baseStart_1547072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547100 : List Nat := [2, 2, 4, 2, 1, 3, 1, 2, 2, 4]
def baseStart_1547100 : Nat := 118140960795 + 1547100 * 2 ^ 59
def prefixEnd_1547100 : Nat := 4983230072969 + 3 ^ 40 * 1547100 * 2
def baseEnd_1547100 : Nat := 264801973523667399278341

theorem tailTrace_1547100 : CollatzResearch.WordTrace tailWord_1547100 prefixEnd_1547100 264801973523667399278341 := by
  unfold tailWord_1547100
  simp only [CollatzResearch.WordTrace]
  refine ⟨28213686347564199244595377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37618248463418932326127169 28213686347564199244595377)
  ·
    refine ⟨21160264760673149433446533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28213686347564199244595377 21160264760673149433446533)
    ·
      refine ⟨3967549642626215518771225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21160264760673149433446533 3967549642626215518771225)
      ·
        refine ⟨2975662231969661639078419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3967549642626215518771225 2975662231969661639078419)
        ·
          refine ⟨4463493347954492458617629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2975662231969661639078419 4463493347954492458617629)
          ·
            refine ⟨1673810005482934671981611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4463493347954492458617629 1673810005482934671981611)
            ·
              refine ⟨2510715008224402007972417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1673810005482934671981611 2510715008224402007972417)
              ·
                refine ⟨1883036256168301505979313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2510715008224402007972417 1883036256168301505979313)
                ·
                  refine ⟨1412277192126226129484485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1883036256168301505979313 1412277192126226129484485)
                  ·
                    refine ⟨264801973523667399278341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1412277192126226129484485 264801973523667399278341)
                    ·
                      rfl

theorem cell23_1547100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_1547100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1547100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1547100 prefixEnd_1547100 := by exact prefixLift 1547100
  have htrace : WordTrace (prefixWord ++ tailWord_1547100) baseStart_1547100 baseEnd_1547100 := by
    simpa [prefixWord, tailWord_1547100, baseEnd_1547100] using wordTrace_append hprefix tailTrace_1547100
  have hstable : (prefixWord ++ tailWord_1547100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547100).length < 2 ^ (prefixWord ++ tailWord_1547100).sum := by decide
  have hdescent : baseEnd_1547100 < baseStart_1547100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547133 : List Nat := [1, 4, 1, 1, 2, 1, 3, 4, 1, 3, 2]
def baseStart_1547133 : Nat := 118140960795 + 1547133 * 2 ^ 59
def prefixEnd_1547133 : Nat := 4983230072969 + 3 ^ 40 * 1547133 * 2
def baseEnd_1547133 : Nat := 794422865432600568722371

theorem tailTrace_1547133 : CollatzResearch.WordTrace tailWord_1547133 prefixEnd_1547133 794422865432600568722371 := by
  unfold tailWord_1547133
  simp only [CollatzResearch.WordTrace]
  refine ⟨56428576304008845125142053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37619050869339230083428035 56428576304008845125142053)
  ·
    refine ⟨10580358057001658460964135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56428576304008845125142053 10580358057001658460964135)
    ·
      refine ⟨15870537085502487691446203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10580358057001658460964135 15870537085502487691446203)
      ·
        refine ⟨23805805628253731537169305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15870537085502487691446203 23805805628253731537169305)
        ·
          refine ⟨17854354221190298652876979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23805805628253731537169305 17854354221190298652876979)
          ·
            refine ⟨26781531331785447979315469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17854354221190298652876979 26781531331785447979315469)
            ·
              refine ⟨10043074249419542992243301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26781531331785447979315469 10043074249419542992243301)
              ·
                refine ⟨1883076421766164311045619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10043074249419542992243301 1883076421766164311045619)
                ·
                  refine ⟨2824614632649246466568429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1883076421766164311045619 2824614632649246466568429)
                  ·
                    refine ⟨1059230487243467424963161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2824614632649246466568429 1059230487243467424963161)
                    ·
                      refine ⟨794422865432600568722371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1059230487243467424963161 794422865432600568722371)
                      ·
                        rfl

theorem cell23_1547133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 4, 1, 3, 2].length) (baseStart_1547133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1547133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1547133 prefixEnd_1547133 := by exact prefixLift 1547133
  have htrace : WordTrace (prefixWord ++ tailWord_1547133) baseStart_1547133 baseEnd_1547133 := by
    simpa [prefixWord, tailWord_1547133, baseEnd_1547133] using wordTrace_append hprefix tailTrace_1547133
  have hstable : (prefixWord ++ tailWord_1547133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547133).length < 2 ^ (prefixWord ++ tailWord_1547133).sum := by decide
  have hdescent : baseEnd_1547133 < baseStart_1547133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547158 : List Nat := [5, 3, 1, 1, 1, 2, 3, 2, 1, 2, 2]
def baseStart_1547158 : Nat := 118140960795 + 1547158 * 2 ^ 59
def prefixEnd_1547158 : Nat := 4983230072969 + 3 ^ 40 * 1547158 * 2
def baseEnd_1547158 : Nat := 794435702448962970909757

theorem tailTrace_1547158 : CollatzResearch.WordTrace tailWord_1547158 prefixEnd_1547158 794435702448962970909757 := by
  unfold tailWord_1547158
  simp only [CollatzResearch.WordTrace]
  refine ⟨3526843008057392149675133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37619658752612182929868085 3526843008057392149675133)
  ·
    refine ⟨1322566128021522056128175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3526843008057392149675133 1322566128021522056128175)
    ·
      refine ⟨1983849192032283084192263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1322566128021522056128175 1983849192032283084192263)
      ·
        refine ⟨2975773788048424626288395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1983849192032283084192263 2975773788048424626288395)
        ·
          refine ⟨4463660682072636939432593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2975773788048424626288395 4463660682072636939432593)
          ·
            refine ⟨3347745511554477704574445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4463660682072636939432593 3347745511554477704574445)
            ·
              refine ⟨1255404566832929139215417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3347745511554477704574445 1255404566832929139215417)
              ·
                refine ⟨941553425124696854411563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1255404566832929139215417 941553425124696854411563)
                ·
                  refine ⟨1412330137687045281617345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 941553425124696854411563 1412330137687045281617345)
                  ·
                    refine ⟨1059247603265283961213009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1412330137687045281617345 1059247603265283961213009)
                    ·
                      refine ⟨794435702448962970909757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1059247603265283961213009 794435702448962970909757)
                      ·
                        rfl

theorem cell23_1547158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_1547158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1547158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1547158 prefixEnd_1547158 := by exact prefixLift 1547158
  have htrace : WordTrace (prefixWord ++ tailWord_1547158) baseStart_1547158 baseEnd_1547158 := by
    simpa [prefixWord, tailWord_1547158, baseEnd_1547158] using wordTrace_append hprefix tailTrace_1547158
  have hstable : (prefixWord ++ tailWord_1547158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547158).length < 2 ^ (prefixWord ++ tailWord_1547158).sum := by decide
  have hdescent : baseEnd_1547158 < baseStart_1547158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547220 : List Nat := [2, 4, 1, 2, 1, 2, 4, 2, 5]
def baseStart_1547220 : Nat := 118140960795 + 1547220 * 2 ^ 59
def prefixEnd_1547220 : Nat := 4983230072969 + 3 ^ 40 * 1547220 * 2
def baseEnd_1547220 : Nat := 88274170916615747592719

theorem tailTrace_1547220 : CollatzResearch.WordTrace tailWord_1547220 prefixEnd_1547220 88274170916615747592719 := by
  unfold tailWord_1547220
  simp only [CollatzResearch.WordTrace]
  refine ⟨28215874727346829491779557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37621166303129105989039409 28215874727346829491779557)
  ·
    refine ⟨5290476511377530529708667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28215874727346829491779557 5290476511377530529708667)
    ·
      refine ⟨7935714767066295794563001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5290476511377530529708667 7935714767066295794563001)
      ·
        refine ⟨5951786075299721845922251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7935714767066295794563001 5951786075299721845922251)
        ·
          refine ⟨8927679112949582768883377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5951786075299721845922251 8927679112949582768883377)
          ·
            refine ⟨6695759334712187076662533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8927679112949582768883377 6695759334712187076662533)
            ·
              refine ⟨1255454875258535076874225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6695759334712187076662533 1255454875258535076874225)
              ·
                refine ⟨941591156443901307655669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1255454875258535076874225 941591156443901307655669)
                ·
                  refine ⟨88274170916615747592719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 941591156443901307655669 88274170916615747592719)
                  ·
                    rfl

theorem cell23_1547220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4, 2, 5].length) (baseStart_1547220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1547220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1547220 prefixEnd_1547220 := by exact prefixLift 1547220
  have htrace : WordTrace (prefixWord ++ tailWord_1547220) baseStart_1547220 baseEnd_1547220 := by
    simpa [prefixWord, tailWord_1547220, baseEnd_1547220] using wordTrace_append hprefix tailTrace_1547220
  have hstable : (prefixWord ++ tailWord_1547220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547220).length < 2 ^ (prefixWord ++ tailWord_1547220).sum := by decide
  have hdescent : baseEnd_1547220 < baseStart_1547220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547226 : List Nat := [3, 1, 1, 2, 4, 1, 2, 1, 1, 2, 5]
def baseStart_1547226 : Nat := 118140960795 + 1547226 * 2 ^ 59
def prefixEnd_1547226 : Nat := 4983230072969 + 3 ^ 40 * 1547226 * 2
def baseEnd_1547226 : Nat := 794470619133468704859443

theorem tailTrace_1547226 : CollatzResearch.WordTrace tailWord_1547226 prefixEnd_1547226 794470619133468704859443 := by
  unfold tailWord_1547226
  simp only [CollatzResearch.WordTrace]
  refine ⟨14107992073167980502069383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37621312195114614672185021 14107992073167980502069383)
  ·
    refine ⟨21161988109751970753104075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14107992073167980502069383 21161988109751970753104075)
    ·
      refine ⟨31742982164627956129656113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21161988109751970753104075 31742982164627956129656113)
      ·
        refine ⟨23807236623470967097242085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31742982164627956129656113 23807236623470967097242085)
        ·
          refine ⟨4463856866900806330732891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23807236623470967097242085 4463856866900806330732891)
          ·
            refine ⟨6695785300351209496099337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4463856866900806330732891 6695785300351209496099337)
            ·
              refine ⟨5021838975263407122074503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6695785300351209496099337 5021838975263407122074503)
              ·
                refine ⟨7532758462895110683111755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5021838975263407122074503 7532758462895110683111755)
                ·
                  refine ⟨11299137694342666024667633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7532758462895110683111755 11299137694342666024667633)
                  ·
                    refine ⟨8474353270756999518500725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11299137694342666024667633 8474353270756999518500725)
                    ·
                      refine ⟨794470619133468704859443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8474353270756999518500725 794470619133468704859443)
                      ·
                        rfl

theorem cell23_1547226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_1547226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1547226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1547226 prefixEnd_1547226 := by exact prefixLift 1547226
  have htrace : WordTrace (prefixWord ++ tailWord_1547226) baseStart_1547226 baseEnd_1547226 := by
    simpa [prefixWord, tailWord_1547226, baseEnd_1547226] using wordTrace_append hprefix tailTrace_1547226
  have hstable : (prefixWord ++ tailWord_1547226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547226).length < 2 ^ (prefixWord ++ tailWord_1547226).sum := by decide
  have hdescent : baseEnd_1547226 < baseStart_1547226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547259 : List Nat := [1, 1, 1, 1, 1, 3, 3, 4, 8]
def baseStart_1547259 : Nat := 118140960795 + 1547259 * 2 ^ 59
def prefixEnd_1547259 : Nat := 4983230072969 + 3 ^ 40 * 1547259 * 2
def baseEnd_1547259 : Nat := 88276395999451897305199

theorem tailTrace_1547259 : CollatzResearch.WordTrace tailWord_1547259 prefixEnd_1547259 88276395999451897305199 := by
  unfold tailWord_1547259
  simp only [CollatzResearch.WordTrace]
  refine ⟨56433171901552368644228831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37622114601034912429485887 56433171901552368644228831)
  ·
    refine ⟨84649757852328552966343247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56433171901552368644228831 84649757852328552966343247)
    ·
      refine ⟨126974636778492829449514871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84649757852328552966343247 126974636778492829449514871)
      ·
        refine ⟨190461955167739244174272307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126974636778492829449514871 190461955167739244174272307)
        ·
          refine ⟨285692932751608866261408461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190461955167739244174272307 285692932751608866261408461)
          ·
            refine ⟨107134849781853324848028173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 285692932751608866261408461 107134849781853324848028173)
            ·
              refine ⟨40175568668194996818010565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107134849781853324848028173 40175568668194996818010565)
              ·
                refine ⟨7532919125286561903376981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40175568668194996818010565 7532919125286561903376981)
                ·
                  refine ⟨88276395999451897305199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7532919125286561903376981 88276395999451897305199)
                  ·
                    rfl

theorem cell23_1547259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 8].length) (baseStart_1547259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1547259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1547259 prefixEnd_1547259 := by exact prefixLift 1547259
  have htrace : WordTrace (prefixWord ++ tailWord_1547259) baseStart_1547259 baseEnd_1547259 := by
    simpa [prefixWord, tailWord_1547259, baseEnd_1547259] using wordTrace_append hprefix tailTrace_1547259
  have hstable : (prefixWord ++ tailWord_1547259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547259).length < 2 ^ (prefixWord ++ tailWord_1547259).sum := by decide
  have hdescent : baseEnd_1547259 < baseStart_1547259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547276 : List Nat := [2, 2, 1, 2, 3, 3, 1, 1, 8]
def baseStart_1547276 : Nat := 118140960795 + 1547276 * 2 ^ 59
def prefixEnd_1547276 : Nat := 4983230072969 + 3 ^ 40 * 1547276 * 2
def baseEnd_1547276 : Nat := 88277365907354834359357

theorem tailTrace_1547276 : CollatzResearch.WordTrace tailWord_1547276 prefixEnd_1547276 88277365907354834359357 := by
  unfold tailWord_1547276
  simp only [CollatzResearch.WordTrace]
  refine ⟨28216895971245390273798841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37622527961660520365065121 28216895971245390273798841)
  ·
    refine ⟨21162671978434042705349131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28216895971245390273798841 21162671978434042705349131)
    ·
      refine ⟨31744007967651064058023697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21162671978434042705349131 31744007967651064058023697)
      ·
        refine ⟨23808005975738298043517773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31744007967651064058023697 23808005975738298043517773)
        ·
          refine ⟨8928002240901861766319165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23808005975738298043517773 8928002240901861766319165)
          ·
            refine ⟨3348000840338198162369687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8928002240901861766319165 3348000840338198162369687)
            ·
              refine ⟨5022001260507297243554531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3348000840338198162369687 5022001260507297243554531)
              ·
                refine ⟨7533001890760945865331797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5022001260507297243554531 7533001890760945865331797)
                ·
                  refine ⟨88277365907354834359357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7533001890760945865331797 88277365907354834359357)
                  ·
                    rfl

theorem cell23_1547276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 8].length) (baseStart_1547276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1547276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1547276 prefixEnd_1547276 := by exact prefixLift 1547276
  have htrace : WordTrace (prefixWord ++ tailWord_1547276) baseStart_1547276 baseEnd_1547276 := by
    simpa [prefixWord, tailWord_1547276, baseEnd_1547276] using wordTrace_append hprefix tailTrace_1547276
  have hstable : (prefixWord ++ tailWord_1547276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547276).length < 2 ^ (prefixWord ++ tailWord_1547276).sum := by decide
  have hdescent : baseEnd_1547276 < baseStart_1547276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547313 : List Nat := [1, 2, 2, 3, 1, 2, 1, 3, 1, 5, 2]
def baseStart_1547313 : Nat := 118140960795 + 1547313 * 2 ^ 59
def prefixEnd_1547313 : Nat := 4983230072969 + 3 ^ 40 * 1547313 * 2
def baseEnd_1547313 : Nat := 794515291950409864471543

theorem tailTrace_1547313 : CollatzResearch.WordTrace tailWord_1547313 prefixEnd_1547313 794515291950409864471543 := by
  unfold tailWord_1547313
  simp only [CollatzResearch.WordTrace]
  refine ⟨56435141443356735866694593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37623427628904490577796395 56435141443356735866694593)
  ·
    refine ⟨42326356082517551900020945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56435141443356735866694593 42326356082517551900020945)
    ·
      refine ⟨31744767061888163925015709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42326356082517551900020945 31744767061888163925015709)
      ·
        refine ⟨11904287648208061471880891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31744767061888163925015709 11904287648208061471880891)
        ·
          refine ⟨17856431472312092207821337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11904287648208061471880891 17856431472312092207821337)
          ·
            refine ⟨13392323604234069155866003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17856431472312092207821337 13392323604234069155866003)
            ·
              refine ⟨20088485406351103733799005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13392323604234069155866003 20088485406351103733799005)
              ·
                refine ⟨7533182027381663900174627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20088485406351103733799005 7533182027381663900174627)
                ·
                  refine ⟨11299773041072495850261941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7533182027381663900174627 11299773041072495850261941)
                  ·
                    refine ⟨1059353722600546485962057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11299773041072495850261941 1059353722600546485962057)
                    ·
                      refine ⟨794515291950409864471543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1059353722600546485962057 794515291950409864471543)
                      ·
                        rfl

theorem cell23_1547313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 5, 2].length) (baseStart_1547313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1547313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1547313 prefixEnd_1547313 := by exact prefixLift 1547313
  have htrace : WordTrace (prefixWord ++ tailWord_1547313) baseStart_1547313 baseEnd_1547313 := by
    simpa [prefixWord, tailWord_1547313, baseEnd_1547313] using wordTrace_append hprefix tailTrace_1547313
  have hstable : (prefixWord ++ tailWord_1547313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547313).length < 2 ^ (prefixWord ++ tailWord_1547313).sum := by decide
  have hdescent : baseEnd_1547313 < baseStart_1547313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547360 : List Nat := [2, 1, 1, 3, 2, 2, 2, 1, 5, 2, 2]
def baseStart_1547360 : Nat := 118140960795 + 1547360 * 2 ^ 59
def prefixEnd_1547360 : Nat := 4983230072969 + 3 ^ 40 * 1547360 * 2
def baseEnd_1547360 : Nat := 794539425541171180583827

theorem tailTrace_1547360 : CollatzResearch.WordTrace tailWord_1547360 prefixEnd_1547360 794539425541171180583827 := by
  unfold tailWord_1547360
  simp only [CollatzResearch.WordTrace]
  refine ⟨28218427837093231446827767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37624570449457641929103689 28218427837093231446827767)
  ·
    refine ⟨42327641755639847170241651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28218427837093231446827767 42327641755639847170241651)
    ·
      refine ⟨63491462633459770755362477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42327641755639847170241651 63491462633459770755362477)
      ·
        refine ⟨23809298487547414033260929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63491462633459770755362477 23809298487547414033260929)
        ·
          refine ⟨17856973865660560524945697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23809298487547414033260929 17856973865660560524945697)
          ·
            refine ⟨13392730399245420393709273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17856973865660560524945697 13392730399245420393709273)
            ·
              refine ⟨10044547799434065295281955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13392730399245420393709273 10044547799434065295281955)
              ·
                refine ⟨15066821699151097942922933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10044547799434065295281955 15066821699151097942922933)
                ·
                  refine ⟨1412514534295415432149025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15066821699151097942922933 1412514534295415432149025)
                  ·
                    refine ⟨1059385900721561574111769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1412514534295415432149025 1059385900721561574111769)
                    ·
                      refine ⟨794539425541171180583827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1059385900721561574111769 794539425541171180583827)
                      ·
                        rfl

theorem cell23_1547360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 5, 2, 2].length) (baseStart_1547360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1547360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1547360 prefixEnd_1547360 := by exact prefixLift 1547360
  have htrace : WordTrace (prefixWord ++ tailWord_1547360) baseStart_1547360 baseEnd_1547360 := by
    simpa [prefixWord, tailWord_1547360, baseEnd_1547360] using wordTrace_append hprefix tailTrace_1547360
  have hstable : (prefixWord ++ tailWord_1547360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547360).length < 2 ^ (prefixWord ++ tailWord_1547360).sum := by decide
  have hdescent : baseEnd_1547360 < baseStart_1547360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547373 : List Nat := [1, 5, 1, 1, 2, 2, 1, 1, 3, 2, 4]
def baseStart_1547373 : Nat := 118140960795 + 1547373 * 2 ^ 59
def prefixEnd_1547373 : Nat := 4983230072969 + 3 ^ 40 * 1547373 * 2
def baseEnd_1547373 : Nat := 794546100789679629721267

theorem tailTrace_1547373 : CollatzResearch.WordTrace tailWord_1547373 prefixEnd_1547373 794546100789679629721267 := by
  unfold tailWord_1547373
  simp only [CollatzResearch.WordTrace]
  refine ⟨56437329823139366113878773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37624886548759577409252515 56437329823139366113878773)
  ·
    refine ⟨5290999670919315573176135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56437329823139366113878773 5290999670919315573176135)
    ·
      refine ⟨7936499506378973359764203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5290999670919315573176135 7936499506378973359764203)
      ·
        refine ⟨11904749259568460039646305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7936499506378973359764203 11904749259568460039646305)
        ·
          refine ⟨8928561944676345029734729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11904749259568460039646305 8928561944676345029734729)
          ·
            refine ⟨6696421458507258772301047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8928561944676345029734729 6696421458507258772301047)
            ·
              refine ⟨10044632187760888158451571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6696421458507258772301047 10044632187760888158451571)
              ·
                refine ⟨15066948281641332237677357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10044632187760888158451571 15066948281641332237677357)
                ·
                  refine ⟨5650105605615499589129009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15066948281641332237677357 5650105605615499589129009)
                  ·
                    refine ⟨4237579204211624691846757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5650105605615499589129009 4237579204211624691846757)
                    ·
                      refine ⟨794546100789679629721267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4237579204211624691846757 794546100789679629721267)
                      ·
                        rfl

theorem cell23_1547373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_1547373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1547373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1547373 prefixEnd_1547373 := by exact prefixLift 1547373
  have htrace : WordTrace (prefixWord ++ tailWord_1547373) baseStart_1547373 baseEnd_1547373 := by
    simpa [prefixWord, tailWord_1547373, baseEnd_1547373] using wordTrace_append hprefix tailTrace_1547373
  have hstable : (prefixWord ++ tailWord_1547373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547373).length < 2 ^ (prefixWord ++ tailWord_1547373).sum := by decide
  have hdescent : baseEnd_1547373 < baseStart_1547373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547400 : List Nat := [2, 1, 3, 4, 2, 2, 1, 8]
def baseStart_1547400 : Nat := 118140960795 + 1547400 * 2 ^ 59
def prefixEnd_1547400 : Nat := 4983230072969 + 3 ^ 40 * 1547400 * 2
def baseEnd_1547400 : Nat := 29428146843235223114209

theorem tailTrace_1547400 : CollatzResearch.WordTrace tailWord_1547400 prefixEnd_1547400 29428146843235223114209 := by
  unfold tailWord_1547400
  simp only [CollatzResearch.WordTrace]
  refine ⟨28219157297020774862555827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37625543062694366483407769 28219157297020774862555827)
  ·
    refine ⟨42328735945531162293833741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28219157297020774862555827 42328735945531162293833741)
    ·
      refine ⟨15873275979574185860187653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42328735945531162293833741 15873275979574185860187653)
      ·
        refine ⟨2976239246170159848785185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15873275979574185860187653 2976239246170159848785185)
        ·
          refine ⟨2232179434627619886588889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2976239246170159848785185 2232179434627619886588889)
          ·
            refine ⟨1674134575970714914941667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2232179434627619886588889 1674134575970714914941667)
            ·
              refine ⟨2511201863956072372412501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1674134575970714914941667 2511201863956072372412501)
              ·
                refine ⟨29428146843235223114209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2511201863956072372412501 29428146843235223114209)
                ·
                  rfl

theorem cell23_1547400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 8].length) (baseStart_1547400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1547400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1547400 prefixEnd_1547400 := by exact prefixLift 1547400
  have htrace : WordTrace (prefixWord ++ tailWord_1547400) baseStart_1547400 baseEnd_1547400 := by
    simpa [prefixWord, tailWord_1547400, baseEnd_1547400] using wordTrace_append hprefix tailTrace_1547400
  have hstable : (prefixWord ++ tailWord_1547400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547400).length < 2 ^ (prefixWord ++ tailWord_1547400).sum := by decide
  have hdescent : baseEnd_1547400 < baseStart_1547400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547410 : List Nat := [3, 2, 3, 1, 1, 2, 1, 3, 1, 3, 3]
def baseStart_1547410 : Nat := 118140960795 + 1547410 * 2 ^ 59
def prefixEnd_1547410 : Nat := 4983230072969 + 3 ^ 40 * 1547410 * 2
def baseEnd_1547410 : Nat := 794565099573895984958597

theorem tailTrace_1547410 : CollatzResearch.WordTrace tailWord_1547410 prefixEnd_1547410 794565099573895984958597 := by
  unfold tailWord_1547410
  simp only [CollatzResearch.WordTrace]
  refine ⟨14109669831001330358243921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37625786216003547621983789 14109669831001330358243921)
  ·
    refine ⟨10582252373250997768682941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14109669831001330358243921 10582252373250997768682941)
    ·
      refine ⟨3968344639969124163256103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10582252373250997768682941 3968344639969124163256103)
      ·
        refine ⟨5952516959953686244884155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3968344639969124163256103 5952516959953686244884155)
        ·
          refine ⟨8928775439930529367326233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5952516959953686244884155 8928775439930529367326233)
          ·
            refine ⟨6696581579947897025494675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8928775439930529367326233 6696581579947897025494675)
            ·
              refine ⟨10044872369921845538242013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6696581579947897025494675 10044872369921845538242013)
              ·
                refine ⟨3766827138720692076840755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10044872369921845538242013 3766827138720692076840755)
                ·
                  refine ⟨5650240708081038115261133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3766827138720692076840755 5650240708081038115261133)
                  ·
                    refine ⟨2118840265530389293222925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5650240708081038115261133 2118840265530389293222925)
                    ·
                      refine ⟨794565099573895984958597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2118840265530389293222925 794565099573895984958597)
                      ·
                        rfl

theorem cell23_1547410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_1547410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1547410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1547410 prefixEnd_1547410 := by exact prefixLift 1547410
  have htrace : WordTrace (prefixWord ++ tailWord_1547410) baseStart_1547410 baseEnd_1547410 := by
    simpa [prefixWord, tailWord_1547410, baseEnd_1547410] using wordTrace_append hprefix tailTrace_1547410
  have hstable : (prefixWord ++ tailWord_1547410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547410).length < 2 ^ (prefixWord ++ tailWord_1547410).sum := by decide
  have hdescent : baseEnd_1547410 < baseStart_1547410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547453 : List Nat := [1, 4, 1, 2, 1, 1, 2, 1, 1, 6, 3]
def baseStart_1547453 : Nat := 118140960795 + 1547453 * 2 ^ 59
def prefixEnd_1547453 : Nat := 4983230072969 + 3 ^ 40 * 1547453 * 2
def baseEnd_1547453 : Nat := 794587179242039316720899

theorem tailTrace_1547453 : CollatzResearch.WordTrace tailWord_1547453 prefixEnd_1547453 794587179242039316720899 := by
  unfold tailWord_1547453
  simp only [CollatzResearch.WordTrace]
  refine ⟨56440247662849539776791013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37626831775233026517860675 56440247662849539776791013)
  ·
    refine ⟨10582546436784288708148315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56440247662849539776791013 10582546436784288708148315)
    ·
      refine ⟨15873819655176433062222473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10582546436784288708148315 15873819655176433062222473)
      ·
        refine ⟨11905364741382324796666855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15873819655176433062222473 11905364741382324796666855)
        ·
          refine ⟨17858047112073487195000283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11905364741382324796666855 17858047112073487195000283)
          ·
            refine ⟨26787070668110230792500425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17858047112073487195000283 26787070668110230792500425)
            ·
              refine ⟨20090303001082673094375319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26787070668110230792500425 20090303001082673094375319)
              ·
                refine ⟨30135454501624009641562979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20090303001082673094375319 30135454501624009641562979)
                ·
                  refine ⟨45203181752436014462344469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30135454501624009641562979 45203181752436014462344469)
                  ·
                    refine ⟨2118899144645438177922397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 45203181752436014462344469 2118899144645438177922397)
                    ·
                      refine ⟨794587179242039316720899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2118899144645438177922397 794587179242039316720899)
                      ·
                        rfl

theorem cell23_1547453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_1547453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1547453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1547453 prefixEnd_1547453 := by exact prefixLift 1547453
  have htrace : WordTrace (prefixWord ++ tailWord_1547453) baseStart_1547453 baseEnd_1547453 := by
    simpa [prefixWord, tailWord_1547453, baseEnd_1547453] using wordTrace_append hprefix tailTrace_1547453
  have hstable : (prefixWord ++ tailWord_1547453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547453).length < 2 ^ (prefixWord ++ tailWord_1547453).sum := by decide
  have hdescent : baseEnd_1547453 < baseStart_1547453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547507 : List Nat := [1, 1, 1, 2, 2, 6, 3, 2, 5]
def baseStart_1547507 : Nat := 118140960795 + 1547507 * 2 ^ 59
def prefixEnd_1547507 : Nat := 4983230072969 + 3 ^ 40 * 1547507 * 2
def baseEnd_1547507 : Nat := 88290545244153567271739

theorem tailTrace_1547507 : CollatzResearch.WordTrace tailWord_1547507 prefixEnd_1547507 88290545244153567271739 := by
  unfold tailWord_1547507
  simp only [CollatzResearch.WordTrace]
  refine ⟨56442217204653906999256775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37628144803102604666171183 56442217204653906999256775)
  ·
    refine ⟨84663325806980860498885163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56442217204653906999256775 84663325806980860498885163)
    ·
      refine ⟨126994988710471290748327745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84663325806980860498885163 126994988710471290748327745)
      ·
        refine ⟨95246241532853468061245809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126994988710471290748327745 95246241532853468061245809)
        ·
          refine ⟨71434681149640101045934357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95246241532853468061245809 71434681149640101045934357)
          ·
            refine ⟨3348500678889379736528173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 71434681149640101045934357 3348500678889379736528173)
            ·
              refine ⟨1255687754583517401198065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3348500678889379736528173 1255687754583517401198065)
              ·
                refine ⟨941765815937638050898549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1255687754583517401198065 941765815937638050898549)
                ·
                  refine ⟨88290545244153567271739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 941765815937638050898549 88290545244153567271739)
                  ·
                    rfl

theorem cell23_1547507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3, 2, 5].length) (baseStart_1547507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1547507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1547507 prefixEnd_1547507 := by exact prefixLift 1547507
  have htrace : WordTrace (prefixWord ++ tailWord_1547507) baseStart_1547507 baseEnd_1547507 := by
    simpa [prefixWord, tailWord_1547507, baseEnd_1547507] using wordTrace_append hprefix tailTrace_1547507
  have hstable : (prefixWord ++ tailWord_1547507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547507).length < 2 ^ (prefixWord ++ tailWord_1547507).sum := by decide
  have hdescent : baseEnd_1547507 < baseStart_1547507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547513 : List Nat := [1, 2, 1, 3, 1, 1, 5, 1, 1, 2, 5]
def baseStart_1547513 : Nat := 118140960795 + 1547513 * 2 ^ 59
def prefixEnd_1547513 : Nat := 4983230072969 + 3 ^ 40 * 1547513 * 2
def baseEnd_1547513 : Nat := 794617988081309081970623

theorem tailTrace_1547513 : CollatzResearch.WordTrace tailWord_1547513 prefixEnd_1547513 794617988081309081970623 := by
  unfold tailWord_1547513
  simp only [CollatzResearch.WordTrace]
  refine ⟨56442436042632170023975193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37628290695088113349316795 56442436042632170023975193)
  ·
    refine ⟨42331827031974127517981395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56442436042632170023975193 42331827031974127517981395)
    ·
      refine ⟨63497740547961191276972093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42331827031974127517981395 63497740547961191276972093)
      ·
        refine ⟨23811652705485446728864535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63497740547961191276972093 23811652705485446728864535)
        ·
          refine ⟨35717479058228170093296803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23811652705485446728864535 35717479058228170093296803)
          ·
            refine ⟨53576218587342255139945205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35717479058228170093296803 53576218587342255139945205)
            ·
              refine ⟨5022770492563336419369863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53576218587342255139945205 5022770492563336419369863)
              ·
                refine ⟨7534155738845004629054795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5022770492563336419369863 7534155738845004629054795)
                ·
                  refine ⟨11301233608267506943582193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7534155738845004629054795 11301233608267506943582193)
                  ·
                    refine ⟨8475925206200630207686645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11301233608267506943582193 8475925206200630207686645)
                    ·
                      refine ⟨794617988081309081970623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8475925206200630207686645 794617988081309081970623)
                      ·
                        rfl

theorem cell23_1547513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_1547513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1547513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1547513 prefixEnd_1547513 := by exact prefixLift 1547513
  have htrace : WordTrace (prefixWord ++ tailWord_1547513) baseStart_1547513 baseEnd_1547513 := by
    simpa [prefixWord, tailWord_1547513, baseEnd_1547513] using wordTrace_append hprefix tailTrace_1547513
  have hstable : (prefixWord ++ tailWord_1547513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547513).length < 2 ^ (prefixWord ++ tailWord_1547513).sum := by decide
  have hdescent : baseEnd_1547513 < baseStart_1547513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547518 : List Nat := [4, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2]
def baseStart_1547518 : Nat := 118140960795 + 1547518 * 2 ^ 59
def prefixEnd_1547518 : Nat := 4983230072969 + 3 ^ 40 * 1547518 * 2
def baseEnd_1547518 : Nat := 794620555484581562408101

theorem tailTrace_1547518 : CollatzResearch.WordTrace tailWord_1547518 prefixEnd_1547518 794620555484581562408101 := by
  unfold tailWord_1547518
  simp only [CollatzResearch.WordTrace]
  refine ⟨7055327300951756984738401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37628412271742703918604805 7055327300951756984738401)
  ·
    refine ⟨5291495475713817738553801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7055327300951756984738401 5291495475713817738553801)
    ·
      refine ⟨3968621606785363303915351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5291495475713817738553801 3968621606785363303915351)
      ·
        refine ⟨5952932410178044955873027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3968621606785363303915351 5952932410178044955873027)
        ·
          refine ⟨8929398615267067433809541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5952932410178044955873027 8929398615267067433809541)
          ·
            refine ⟨1674262240362575143839289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8929398615267067433809541 1674262240362575143839289)
            ·
              refine ⟨1255696680271931357879467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1674262240362575143839289 1255696680271931357879467)
              ·
                refine ⟨1883545020407897036819201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1255696680271931357879467 1883545020407897036819201)
                ·
                  refine ⟨1412658765305922777614401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1883545020407897036819201 1412658765305922777614401)
                  ·
                    refine ⟨1059494073979442083210801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1412658765305922777614401 1059494073979442083210801)
                    ·
                      refine ⟨794620555484581562408101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1059494073979442083210801 794620555484581562408101)
                      ·
                        rfl

theorem cell23_1547518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_1547518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1547518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1547518 prefixEnd_1547518 := by exact prefixLift 1547518
  have htrace : WordTrace (prefixWord ++ tailWord_1547518) baseStart_1547518 baseEnd_1547518 := by
    simpa [prefixWord, tailWord_1547518, baseEnd_1547518] using wordTrace_append hprefix tailTrace_1547518
  have hstable : (prefixWord ++ tailWord_1547518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547518).length < 2 ^ (prefixWord ++ tailWord_1547518).sum := by decide
  have hdescent : baseEnd_1547518 < baseStart_1547518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547553 : List Nat := [1, 2, 3, 2, 1, 1, 1, 3, 2, 1, 6]
def baseStart_1547553 : Nat := 118140960795 + 1547553 * 2 ^ 59
def prefixEnd_1547553 : Nat := 4983230072969 + 3 ^ 40 * 1547553 * 2
def baseEnd_1547553 : Nat := 794638527307488925470439

theorem tailTrace_1547553 : CollatzResearch.WordTrace tailWord_1547553 prefixEnd_1547553 794638527307488925470439 := by
  unfold tailWord_1547553
  simp only [CollatzResearch.WordTrace]
  refine ⟨56443894962487256855431313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37629263308324837903620875 56443894962487256855431313)
  ·
    refine ⟨42332921221865442641573485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56443894962487256855431313 42332921221865442641573485)
    ·
      refine ⟨15874845458199540990590057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42332921221865442641573485 15874845458199540990590057)
      ·
        refine ⟨11906134093649655742942543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15874845458199540990590057 11906134093649655742942543)
        ·
          refine ⟨17859201140474483614413815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11906134093649655742942543 17859201140474483614413815)
          ·
            refine ⟨26788801710711725421620723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17859201140474483614413815 26788801710711725421620723)
            ·
              refine ⟨40183202566067588132431085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26788801710711725421620723 40183202566067588132431085)
              ·
                refine ⟨15068700962275345549661657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40183202566067588132431085 15068700962275345549661657)
                ·
                  refine ⟨11301525721706509162246243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15068700962275345549661657 11301525721706509162246243)
                  ·
                    refine ⟨16952288582559763743369365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11301525721706509162246243 16952288582559763743369365)
                    ·
                      refine ⟨794638527307488925470439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16952288582559763743369365 794638527307488925470439)
                      ·
                        rfl

theorem cell23_1547553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_1547553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1547553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1547553 prefixEnd_1547553 := by exact prefixLift 1547553
  have htrace : WordTrace (prefixWord ++ tailWord_1547553) baseStart_1547553 baseEnd_1547553 := by
    simpa [prefixWord, tailWord_1547553, baseEnd_1547553] using wordTrace_append hprefix tailTrace_1547553
  have hstable : (prefixWord ++ tailWord_1547553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547553).length < 2 ^ (prefixWord ++ tailWord_1547553).sum := by decide
  have hdescent : baseEnd_1547553 < baseStart_1547553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547580 : List Nat := [2, 2, 2, 2, 1, 3, 2, 3, 6]
def baseStart_1547580 : Nat := 118140960795 + 1547580 * 2 ^ 59
def prefixEnd_1547580 : Nat := 4983230072969 + 3 ^ 40 * 1547580 * 2
def baseEnd_1547580 : Nat := 88294710142795591092535

theorem tailTrace_1547580 : CollatzResearch.WordTrace tailWord_1547580 prefixEnd_1547580 88294710142795591092535 := by
  unfold tailWord_1547580
  simp only [CollatzResearch.WordTrace]
  refine ⟨28222439866694720233332097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37629919822259626977776129 28222439866694720233332097)
  ·
    refine ⟨21166829900021040174999073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28222439866694720233332097 21166829900021040174999073)
    ·
      refine ⟨15875122425015780131249305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21166829900021040174999073 15875122425015780131249305)
      ·
        refine ⟨11906341818761835098436979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15875122425015780131249305 11906341818761835098436979)
        ·
          refine ⟨17859512728142752647655469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11906341818761835098436979 17859512728142752647655469)
          ·
            refine ⟨6697317273053532242870801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17859512728142752647655469 6697317273053532242870801)
            ·
              refine ⟨5022987954790149182153101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6697317273053532242870801 5022987954790149182153101)
              ·
                refine ⟨1883620483046305943307413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5022987954790149182153101 1883620483046305943307413)
                ·
                  refine ⟨88294710142795591092535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1883620483046305943307413 88294710142795591092535)
                  ·
                    rfl

theorem cell23_1547580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 3, 6].length) (baseStart_1547580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1547580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1547580 prefixEnd_1547580 := by exact prefixLift 1547580
  have htrace : WordTrace (prefixWord ++ tailWord_1547580) baseStart_1547580 baseEnd_1547580 := by
    simpa [prefixWord, tailWord_1547580, baseEnd_1547580] using wordTrace_append hprefix tailTrace_1547580
  have hstable : (prefixWord ++ tailWord_1547580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547580).length < 2 ^ (prefixWord ++ tailWord_1547580).sum := by decide
  have hdescent : baseEnd_1547580 < baseStart_1547580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547617 : List Nat := [1, 2, 3, 1, 1, 1, 1, 6, 2, 3, 2]
def baseStart_1547617 : Nat := 118140960795 + 1547617 * 2 ^ 59
def prefixEnd_1547617 : Nat := 4983230072969 + 3 ^ 40 * 1547617 * 2
def baseEnd_1547617 : Nat := 794671390069376675070145

theorem tailTrace_1547617 : CollatzResearch.WordTrace tailWord_1547617 prefixEnd_1547617 794671390069376675070145 := by
  unfold tailWord_1547617
  simp only [CollatzResearch.WordTrace]
  refine ⟨56446229234255395785761105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37630819489503597190507403 56446229234255395785761105)
  ·
    refine ⟨42334671925691546839320829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56446229234255395785761105 42334671925691546839320829)
    ·
      refine ⟨15875501972134330064745311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42334671925691546839320829 15875501972134330064745311)
      ·
        refine ⟨23813252958201495097117967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15875501972134330064745311 23813252958201495097117967)
        ·
          refine ⟨35719879437302242645676951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23813252958201495097117967 35719879437302242645676951)
          ·
            refine ⟨53579819155953363968515427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35719879437302242645676951 53579819155953363968515427)
            ·
              refine ⟨80369728733930045952773141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53579819155953363968515427 80369728733930045952773141)
              ·
                refine ⟨3767331034402970904036241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 80369728733930045952773141 3767331034402970904036241)
                ·
                  refine ⟨2825498275802228178027181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3767331034402970904036241 2825498275802228178027181)
                  ·
                    refine ⟨1059561853425835566760193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2825498275802228178027181 1059561853425835566760193)
                    ·
                      refine ⟨794671390069376675070145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1059561853425835566760193 794671390069376675070145)
                      ·
                        rfl

theorem cell23_1547617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6, 2, 3, 2].length) (baseStart_1547617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1547617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1547617 prefixEnd_1547617 := by exact prefixLift 1547617
  have htrace : WordTrace (prefixWord ++ tailWord_1547617) baseStart_1547617 baseEnd_1547617 := by
    simpa [prefixWord, tailWord_1547617, baseEnd_1547617] using wordTrace_append hprefix tailTrace_1547617
  have hstable : (prefixWord ++ tailWord_1547617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547617).length < 2 ^ (prefixWord ++ tailWord_1547617).sum := by decide
  have hdescent : baseEnd_1547617 < baseStart_1547617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547660 : List Nat := [2, 2, 1, 2, 1, 3, 2, 1, 3, 2, 4]
def baseStart_1547660 : Nat := 118140960795 + 1547660 * 2 ^ 59
def prefixEnd_1547660 : Nat := 4983230072969 + 3 ^ 40 * 1547660 * 2
def baseEnd_1547660 : Nat := 794693469737520006832447

theorem tailTrace_1547660 : CollatzResearch.WordTrace tailWord_1547660 prefixEnd_1547660 794693469737520006832447 := by
  unfold tailWord_1547660
  simp only [CollatzResearch.WordTrace]
  refine ⟨28223898786549807064788217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37631865048733076086384289 28223898786549807064788217)
  ·
    refine ⟨21167924089912355298591163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28223898786549807064788217 21167924089912355298591163)
    ·
      refine ⟨31751886134868532947886745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21167924089912355298591163 31751886134868532947886745)
      ·
        refine ⟨23813914601151399710915059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31751886134868532947886745 23813914601151399710915059)
        ·
          refine ⟨35720871901727099566372589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23813914601151399710915059 35720871901727099566372589)
          ·
            refine ⟨13395326963147662337389721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35720871901727099566372589 13395326963147662337389721)
            ·
              refine ⟨10046495222360746753042291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13395326963147662337389721 10046495222360746753042291)
              ·
                refine ⟨15069742833541120129563437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10046495222360746753042291 15069742833541120129563437)
                ·
                  refine ⟨5651153562577920048586289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15069742833541120129563437 5651153562577920048586289)
                  ·
                    refine ⟨4238365171933440036439717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5651153562577920048586289 4238365171933440036439717)
                    ·
                      refine ⟨794693469737520006832447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4238365171933440036439717 794693469737520006832447)
                      ·
                        rfl

theorem cell23_1547660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_1547660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1547660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1547660 prefixEnd_1547660 := by exact prefixLift 1547660
  have htrace : WordTrace (prefixWord ++ tailWord_1547660) baseStart_1547660 baseEnd_1547660 := by
    simpa [prefixWord, tailWord_1547660, baseEnd_1547660] using wordTrace_append hprefix tailTrace_1547660
  have hstable : (prefixWord ++ tailWord_1547660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547660).length < 2 ^ (prefixWord ++ tailWord_1547660).sum := by decide
  have hdescent : baseEnd_1547660 < baseStart_1547660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547697 : List Nat := [1, 2, 2, 4, 1, 1, 2, 3, 1, 3, 3]
def baseStart_1547697 : Nat := 118140960795 + 1547697 * 2 ^ 59
def prefixEnd_1547697 : Nat := 4983230072969 + 3 ^ 40 * 1547697 * 2
def baseEnd_1547697 : Nat := 794712468521736362069777

theorem tailTrace_1547697 : CollatzResearch.WordTrace tailWord_1547697 prefixEnd_1547697 794712468521736362069777 := by
  unfold tailWord_1547697
  simp only [CollatzResearch.WordTrace]
  refine ⟨56449147073965569448673345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37632764715977046299115563 56449147073965569448673345)
  ·
    refine ⟨42336860305474177086505009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56449147073965569448673345 42336860305474177086505009)
    ·
      refine ⟨31752645229105632814878757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42336860305474177086505009 31752645229105632814878757)
      ·
        refine ⟨5953620980457306152789767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31752645229105632814878757 5953620980457306152789767)
        ·
          refine ⟨8930431470685959229184651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5953620980457306152789767 8930431470685959229184651)
          ·
            refine ⟨13395647206028938843776977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8930431470685959229184651 13395647206028938843776977)
            ·
              refine ⟨10046735404521704132832733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13395647206028938843776977 10046735404521704132832733)
              ·
                refine ⟨3767525776695639049812275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10046735404521704132832733 3767525776695639049812275)
                ·
                  refine ⟨5651288665043458574718413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3767525776695639049812275 5651288665043458574718413)
                  ·
                    refine ⟨2119233249391296965519405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5651288665043458574718413 2119233249391296965519405)
                    ·
                      refine ⟨794712468521736362069777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2119233249391296965519405 794712468521736362069777)
                      ·
                        rfl

theorem cell23_1547697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_1547697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1547697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1547697 prefixEnd_1547697 := by exact prefixLift 1547697
  have htrace : WordTrace (prefixWord ++ tailWord_1547697) baseStart_1547697 baseEnd_1547697 := by
    simpa [prefixWord, tailWord_1547697, baseEnd_1547697] using wordTrace_append hprefix tailTrace_1547697
  have hstable : (prefixWord ++ tailWord_1547697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547697).length < 2 ^ (prefixWord ++ tailWord_1547697).sum := by decide
  have hdescent : baseEnd_1547697 < baseStart_1547697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547701 : List Nat := [1, 3, 3, 2, 2, 3, 1, 2, 1, 2, 3]
def baseStart_1547701 : Nat := 118140960795 + 1547701 * 2 ^ 59
def prefixEnd_1547701 : Nat := 4983230072969 + 3 ^ 40 * 1547701 * 2
def baseEnd_1547701 : Nat := 794714522444354346419759

theorem tailTrace_1547701 : CollatzResearch.WordTrace tailWord_1547701 prefixEnd_1547701 794714522444354346419759 := by
  unfold tailWord_1547701
  simp only [CollatzResearch.WordTrace]
  refine ⟨56449292965951078131818957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37632861977300718754545971 56449292965951078131818957)
  ·
    refine ⟨21168484862231654299432109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56449292965951078131818957 21168484862231654299432109)
    ·
      refine ⟨7938181823336870362287041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21168484862231654299432109 7938181823336870362287041)
      ·
        refine ⟨5953636367502652771715281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7938181823336870362287041 5953636367502652771715281)
        ·
          refine ⟨4465227275626989578786461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5953636367502652771715281 4465227275626989578786461)
          ·
            refine ⟨1674460228360121092044923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4465227275626989578786461 1674460228360121092044923)
            ·
              refine ⟨2511690342540181638067385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1674460228360121092044923 2511690342540181638067385)
              ·
                refine ⟨1883767756905136228550539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2511690342540181638067385 1883767756905136228550539)
                ·
                  refine ⟨2825651635357704342825809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1883767756905136228550539 2825651635357704342825809)
                  ·
                    refine ⟨2119238726518278257119357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2825651635357704342825809 2119238726518278257119357)
                    ·
                      refine ⟨794714522444354346419759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2119238726518278257119357 794714522444354346419759)
                      ·
                        rfl

theorem cell23_1547701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_1547701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1547701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1547701 prefixEnd_1547701 := by exact prefixLift 1547701
  have htrace : WordTrace (prefixWord ++ tailWord_1547701) baseStart_1547701 baseEnd_1547701 := by
    simpa [prefixWord, tailWord_1547701, baseEnd_1547701] using wordTrace_append hprefix tailTrace_1547701
  have hstable : (prefixWord ++ tailWord_1547701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547701).length < 2 ^ (prefixWord ++ tailWord_1547701).sum := by decide
  have hdescent : baseEnd_1547701 < baseStart_1547701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547732 : List Nat := [2, 4, 1, 2, 3, 2, 2, 2, 1, 2, 2]
def baseStart_1547732 : Nat := 118140960795 + 1547732 * 2 ^ 59
def prefixEnd_1547732 : Nat := 4983230072969 + 3 ^ 40 * 1547732 * 2
def baseEnd_1547732 : Nat := 794730440344643725132117

theorem tailTrace_1547732 : CollatzResearch.WordTrace tailWord_1547732 prefixEnd_1547732 794730440344643725132117 := by
  unfold tailWord_1547732
  simp only [CollatzResearch.WordTrace]
  refine ⟨28225211814419385213098725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37633615752559180284131633 28225211814419385213098725)
  ·
    refine ⟨5292227215203634727456011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28225211814419385213098725 5292227215203634727456011)
    ·
      refine ⟨7938340822805452091184017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5292227215203634727456011 7938340822805452091184017)
      ·
        refine ⟨5953755617104089068388013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7938340822805452091184017 5953755617104089068388013)
        ·
          refine ⟨2232658356414033400645505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5953755617104089068388013 2232658356414033400645505)
          ·
            refine ⟨1674493767310525050484129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2232658356414033400645505 1674493767310525050484129)
            ·
              refine ⟨1255870325482893787863097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1674493767310525050484129 1255870325482893787863097)
              ·
                refine ⟨941902744112170340897323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1255870325482893787863097 941902744112170340897323)
                ·
                  refine ⟨1412854116168255511345985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 941902744112170340897323 1412854116168255511345985)
                  ·
                    refine ⟨1059640587126191633509489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1412854116168255511345985 1059640587126191633509489)
                    ·
                      refine ⟨794730440344643725132117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1059640587126191633509489 794730440344643725132117)
                      ·
                        rfl

theorem cell23_1547732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_1547732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1547732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1547732 prefixEnd_1547732 := by exact prefixLift 1547732
  have htrace : WordTrace (prefixWord ++ tailWord_1547732) baseStart_1547732 baseEnd_1547732 := by
    simpa [prefixWord, tailWord_1547732, baseEnd_1547732] using wordTrace_append hprefix tailTrace_1547732
  have hstable : (prefixWord ++ tailWord_1547732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547732).length < 2 ^ (prefixWord ++ tailWord_1547732).sum := by decide
  have hdescent : baseEnd_1547732 < baseStart_1547732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547747 : List Nat := [1, 1, 1, 6, 2, 2, 1, 1, 2, 6]
def baseStart_1547747 : Nat := 118140960795 + 1547747 * 2 ^ 59
def prefixEnd_1547747 : Nat := 4983230072969 + 3 ^ 40 * 1547747 * 2
def baseEnd_1547747 : Nat := 264912714184820388814849

theorem tailTrace_1547747 : CollatzResearch.WordTrace tailWord_1547747 prefixEnd_1547747 264912714184820388814849 := by
  unfold tailWord_1547747
  simp only [CollatzResearch.WordTrace]
  refine ⟨56450970723784427987993495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37633980482522951991995663 56450970723784427987993495)
  ·
    refine ⟨84676456085676641981990243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56450970723784427987993495 84676456085676641981990243)
    ·
      refine ⟨127014684128514962972985365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84676456085676641981990243 127014684128514962972985365)
      ·
        refine ⟨5953813318524138889358689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 127014684128514962972985365 5953813318524138889358689)
        ·
          refine ⟨4465359988893104167019017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5953813318524138889358689 4465359988893104167019017)
          ·
            refine ⟨3349019991669828125264263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4465359988893104167019017 3349019991669828125264263)
            ·
              refine ⟨5023529987504742187896395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3349019991669828125264263 5023529987504742187896395)
              ·
                refine ⟨7535294981257113281844593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5023529987504742187896395 7535294981257113281844593)
                ·
                  refine ⟨5651471235942834961383445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7535294981257113281844593 5651471235942834961383445)
                  ·
                    refine ⟨264912714184820388814849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5651471235942834961383445 264912714184820388814849)
                    ·
                      rfl

theorem cell23_1547747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 2, 6].length) (baseStart_1547747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1547747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1547747 prefixEnd_1547747 := by exact prefixLift 1547747
  have htrace : WordTrace (prefixWord ++ tailWord_1547747) baseStart_1547747 baseEnd_1547747 := by
    simpa [prefixWord, tailWord_1547747, baseEnd_1547747] using wordTrace_append hprefix tailTrace_1547747
  have hstable : (prefixWord ++ tailWord_1547747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547747).length < 2 ^ (prefixWord ++ tailWord_1547747).sum := by decide
  have hdescent : baseEnd_1547747 < baseStart_1547747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547760 : List Nat := [2, 1, 1, 1, 3, 4, 1, 1, 9]
def baseStart_1547760 : Nat := 118140960795 + 1547760 * 2 ^ 59
def prefixEnd_1547760 : Nat := 4983230072969 + 3 ^ 40 * 1547760 * 2
def baseEnd_1547760 : Nat := 88304979755885512842443

theorem tailTrace_1547760 : CollatzResearch.WordTrace tailWord_1547760 prefixEnd_1547760 88304979755885512842443 := by
  unfold tailWord_1547760
  simp only [CollatzResearch.WordTrace]
  refine ⟨28225722436368665604108367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37634296581824887472144489 28225722436368665604108367)
  ·
    refine ⟨42338583654552998406162551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28225722436368665604108367 42338583654552998406162551)
    ·
      refine ⟨63507875481829497609243827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42338583654552998406162551 63507875481829497609243827)
      ·
        refine ⟨95261813222744246413865741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63507875481829497609243827 95261813222744246413865741)
        ·
          refine ⟨35723179958529092405199653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95261813222744246413865741 35723179958529092405199653)
          ·
            refine ⟨6698096242224204825974935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35723179958529092405199653 6698096242224204825974935)
            ·
              refine ⟨10047144363336307238962403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6698096242224204825974935 10047144363336307238962403)
              ·
                refine ⟨15070716545004460858443605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10047144363336307238962403 15070716545004460858443605)
                ·
                  refine ⟨88304979755885512842443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 15070716545004460858443605 88304979755885512842443)
                  ·
                    rfl

theorem cell23_1547760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 9].length) (baseStart_1547760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1547760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1547760 prefixEnd_1547760 := by exact prefixLift 1547760
  have htrace : WordTrace (prefixWord ++ tailWord_1547760) baseStart_1547760 baseEnd_1547760 := by
    simpa [prefixWord, tailWord_1547760, baseEnd_1547760] using wordTrace_append hprefix tailTrace_1547760
  have hstable : (prefixWord ++ tailWord_1547760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547760).length < 2 ^ (prefixWord ++ tailWord_1547760).sum := by decide
  have hdescent : baseEnd_1547760 < baseStart_1547760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547827 : List Nat := [1, 1, 1, 2, 4, 3, 2, 1, 1, 3, 4]
def baseStart_1547827 : Nat := 118140960795 + 1547827 * 2 ^ 59
def prefixEnd_1547827 : Nat := 4983230072969 + 3 ^ 40 * 1547827 * 2
def baseEnd_1547827 : Nat := 794779221006820853444179

theorem tailTrace_1547827 : CollatzResearch.WordTrace tailWord_1547827 prefixEnd_1547827 794779221006820853444179 := by
  unfold tailWord_1547827
  simp only [CollatzResearch.WordTrace]
  refine ⟨56453888563494601650905735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37635925708996401100603823 56453888563494601650905735)
  ·
    refine ⟨84680832845241902476358603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56453888563494601650905735 84680832845241902476358603)
    ·
      refine ⟨127021249267862853714537905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84680832845241902476358603 127021249267862853714537905)
      ·
        refine ⟨95265936950897140285903429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127021249267862853714537905 95265936950897140285903429)
        ·
          refine ⟨17862363178293213803606893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95265936950897140285903429 17862363178293213803606893)
          ·
            refine ⟨6698386191859955176352585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17862363178293213803606893 6698386191859955176352585)
            ·
              refine ⟨5023789643894966382264439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6698386191859955176352585 5023789643894966382264439)
              ·
                refine ⟨7535684465842449573396659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5023789643894966382264439 7535684465842449573396659)
                ·
                  refine ⟨11303526698763674360094989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7535684465842449573396659 11303526698763674360094989)
                  ·
                    refine ⟨4238822512036377885035621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11303526698763674360094989 4238822512036377885035621)
                    ·
                      refine ⟨794779221006820853444179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4238822512036377885035621 794779221006820853444179)
                      ·
                        rfl

theorem cell23_1547827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 3, 4].length) (baseStart_1547827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1547827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1547827 prefixEnd_1547827 := by exact prefixLift 1547827
  have htrace : WordTrace (prefixWord ++ tailWord_1547827) baseStart_1547827 baseEnd_1547827 := by
    simpa [prefixWord, tailWord_1547827, baseEnd_1547827] using wordTrace_append hprefix tailTrace_1547827
  have hstable : (prefixWord ++ tailWord_1547827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547827).length < 2 ^ (prefixWord ++ tailWord_1547827).sum := by decide
  have hdescent : baseEnd_1547827 < baseStart_1547827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547905 : List Nat := [1, 2, 4, 2, 1, 4, 2, 2, 1, 4]
def baseStart_1547905 : Nat := 118140960795 + 1547905 * 2 ^ 59
def prefixEnd_1547905 : Nat := 4983230072969 + 3 ^ 40 * 1547905 * 2
def baseEnd_1547905 : Nat := 264939757499290516089607

theorem tailTrace_1547905 : CollatzResearch.WordTrace tailWord_1547905 prefixEnd_1547905 264939757499290516089607 := by
  unfold tailWord_1547905
  simp only [CollatzResearch.WordTrace]
  refine ⟨56456733457212020972245169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37637822304808013981496779 56456733457212020972245169)
  ·
    refine ⟨42342550092909015729183877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56456733457212020972245169 42342550092909015729183877)
    ·
      refine ⟨7939228142420440449221977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42342550092909015729183877 7939228142420440449221977)
      ·
        refine ⟨5954421106815330336916483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7939228142420440449221977 5954421106815330336916483)
        ·
          refine ⟨8931631660222995505374725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5954421106815330336916483 8931631660222995505374725)
          ·
            refine ⟨1674680936291811657257761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8931631660222995505374725 1674680936291811657257761)
            ·
              refine ⟨1256010702218858742943321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1674680936291811657257761 1256010702218858742943321)
              ·
                refine ⟨942008026664144057207491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1256010702218858742943321 942008026664144057207491)
                ·
                  refine ⟨1413012039996216085811237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 942008026664144057207491 1413012039996216085811237)
                  ·
                    refine ⟨264939757499290516089607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1413012039996216085811237 264939757499290516089607)
                    ·
                      rfl

theorem cell23_1547905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2, 2, 1, 4].length) (baseStart_1547905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1547905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1547905 prefixEnd_1547905 := by exact prefixLift 1547905
  have htrace : WordTrace (prefixWord ++ tailWord_1547905) baseStart_1547905 baseEnd_1547905 := by
    simpa [prefixWord, tailWord_1547905, baseEnd_1547905] using wordTrace_append hprefix tailTrace_1547905
  have hstable : (prefixWord ++ tailWord_1547905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547905).length < 2 ^ (prefixWord ++ tailWord_1547905).sum := by decide
  have hdescent : baseEnd_1547905 < baseStart_1547905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547914 : List Nat := [3, 1, 2, 3, 2, 1, 1, 2, 3, 5]
def baseStart_1547914 : Nat := 118140960795 + 1547914 * 2 ^ 59
def prefixEnd_1547914 : Nat := 4983230072969 + 3 ^ 40 * 1547914 * 2
def baseEnd_1547914 : Nat := 264941297941254004352093

theorem tailTrace_1547914 : CollatzResearch.WordTrace tailWord_1547914 prefixEnd_1547914 264941297941254004352093 := by
  unfold tailWord_1547914
  simp only [CollatzResearch.WordTrace]
  refine ⟨14114265428544853877330699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37638041142786277006215197 14114265428544853877330699)
  ·
    refine ⟨21171398142817280815996049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14114265428544853877330699 21171398142817280815996049)
    ·
      refine ⟨15878548607112960611997037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21171398142817280815996049 15878548607112960611997037)
      ·
        refine ⟨5954455727667360229498889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15878548607112960611997037 5954455727667360229498889)
        ·
          refine ⟨4465841795750520172124167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5954455727667360229498889 4465841795750520172124167)
          ·
            refine ⟨6698762693625780258186251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4465841795750520172124167 6698762693625780258186251)
            ·
              refine ⟨10048144040438670387279377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6698762693625780258186251 10048144040438670387279377)
              ·
                refine ⟨7536108030329002790459533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10048144040438670387279377 7536108030329002790459533)
                ·
                  refine ⟨2826040511373376046422325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7536108030329002790459533 2826040511373376046422325)
                  ·
                    refine ⟨264941297941254004352093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2826040511373376046422325 264941297941254004352093)
                    ·
                      rfl

theorem cell23_1547914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 3, 5].length) (baseStart_1547914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1547914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1547914 prefixEnd_1547914 := by exact prefixLift 1547914
  have htrace : WordTrace (prefixWord ++ tailWord_1547914) baseStart_1547914 baseEnd_1547914 := by
    simpa [prefixWord, tailWord_1547914, baseEnd_1547914] using wordTrace_append hprefix tailTrace_1547914
  have hstable : (prefixWord ++ tailWord_1547914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547914).length < 2 ^ (prefixWord ++ tailWord_1547914).sum := by decide
  have hdescent : baseEnd_1547914 < baseStart_1547914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547951 : List Nat := [1, 1, 2, 1, 2, 4, 1, 2, 5, 2, 2]
def baseStart_1547951 : Nat := 118140960795 + 1547951 * 2 ^ 59
def prefixEnd_1547951 : Nat := 4983230072969 + 3 ^ 40 * 1547951 * 2
def baseEnd_1547951 : Nat := 794842892607978368293609

theorem tailTrace_1547951 : CollatzResearch.WordTrace tailWord_1547951 prefixEnd_1547951 794842892607978368293609 := by
  unfold tailWord_1547951
  simp only [CollatzResearch.WordTrace]
  refine ⟨56458411215045370828419707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37638940810030247218946471 56458411215045370828419707)
  ·
    refine ⟨84687616822568056242629561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56458411215045370828419707 84687616822568056242629561)
    ·
      refine ⟨63515712616926042181972171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84687616822568056242629561 63515712616926042181972171)
      ·
        refine ⟨95273568925389063272958257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63515712616926042181972171 95273568925389063272958257)
        ·
          refine ⟨71455176694041797454718693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95273568925389063272958257 71455176694041797454718693)
          ·
            refine ⟨13397845630132837022759755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71455176694041797454718693 13397845630132837022759755)
            ·
              refine ⟨20096768445199255534139633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13397845630132837022759755 20096768445199255534139633)
              ·
                refine ⟨15072576333899441650604725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20096768445199255534139633 15072576333899441650604725)
                ·
                  refine ⟨1413054031303072654744193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15072576333899441650604725 1413054031303072654744193)
                  ·
                    refine ⟨1059790523477304491058145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1413054031303072654744193 1059790523477304491058145)
                    ·
                      refine ⟨794842892607978368293609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1059790523477304491058145 794842892607978368293609)
                      ·
                        rfl

theorem cell23_1547951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 5, 2, 2].length) (baseStart_1547951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1547951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1547951 prefixEnd_1547951 := by exact prefixLift 1547951
  have htrace : WordTrace (prefixWord ++ tailWord_1547951) baseStart_1547951 baseEnd_1547951 := by
    simpa [prefixWord, tailWord_1547951, baseEnd_1547951] using wordTrace_append hprefix tailTrace_1547951
  have hstable : (prefixWord ++ tailWord_1547951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547951).length < 2 ^ (prefixWord ++ tailWord_1547951).sum := by decide
  have hdescent : baseEnd_1547951 < baseStart_1547951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547961 : List Nat := [1, 2, 1, 4, 1, 1, 5, 2, 2, 4]
def baseStart_1547961 : Nat := 118140960795 + 1547961 * 2 ^ 59
def prefixEnd_1547961 : Nat := 4983230072969 + 3 ^ 40 * 1547961 * 2
def baseEnd_1547961 : Nat := 264949342471507776389521

theorem tailTrace_1547961 : CollatzResearch.WordTrace tailWord_1547961 prefixEnd_1547961 264949342471507776389521 := by
  unfold tailWord_1547961
  simp only [CollatzResearch.WordTrace]
  refine ⟨56458775945009142536283737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37639183963339428357522491 56458775945009142536283737)
  ·
    refine ⟨42344081958756856902212803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56458775945009142536283737 42344081958756856902212803)
    ·
      refine ⟨63516122938135285353319205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42344081958756856902212803 63516122938135285353319205)
      ·
        refine ⟨11909273050900366003747351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63516122938135285353319205 11909273050900366003747351)
        ·
          refine ⟨17863909576350549005621027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11909273050900366003747351 17863909576350549005621027)
          ·
            refine ⟨26795864364525823508431541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17863909576350549005621027 26795864364525823508431541)
            ·
              refine ⟨2512112284174295953915457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26795864364525823508431541 2512112284174295953915457)
              ·
                refine ⟨1884084213130721965436593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2512112284174295953915457 1884084213130721965436593)
                ·
                  refine ⟨1413063159848041474077445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1884084213130721965436593 1413063159848041474077445)
                  ·
                    refine ⟨264949342471507776389521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1413063159848041474077445 264949342471507776389521)
                    ·
                      rfl

theorem cell23_1547961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 2, 2, 4].length) (baseStart_1547961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1547961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1547961 prefixEnd_1547961 := by exact prefixLift 1547961
  have htrace : WordTrace (prefixWord ++ tailWord_1547961) baseStart_1547961 baseEnd_1547961 := by
    simpa [prefixWord, tailWord_1547961, baseEnd_1547961] using wordTrace_append hprefix tailTrace_1547961
  have hstable : (prefixWord ++ tailWord_1547961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547961).length < 2 ^ (prefixWord ++ tailWord_1547961).sum := by decide
  have hdescent : baseEnd_1547961 < baseStart_1547961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547968 : List Nat := [2, 1, 1, 2, 4, 1, 4, 1, 3, 2, 2]
def baseStart_1547968 : Nat := 118140960795 + 1547968 * 2 ^ 59
def prefixEnd_1547968 : Nat := 4983230072969 + 3 ^ 40 * 1547968 * 2
def baseEnd_1547968 : Nat := 794851621779104801781031

theorem tailTrace_1547968 : CollatzResearch.WordTrace tailWord_1547968 prefixEnd_1547968 794851621779104801781031 := by
  unfold tailWord_1547968
  simp only [CollatzResearch.WordTrace]
  refine ⟨28229515627991891365894279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37639354170655855154525705 28229515627991891365894279)
  ·
    refine ⟨42344273441987837048841419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28229515627991891365894279 42344273441987837048841419)
    ·
      refine ⟨63516410162981755573262129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42344273441987837048841419 63516410162981755573262129)
      ·
        refine ⟨47637307622236316679946597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63516410162981755573262129 47637307622236316679946597)
        ·
          refine ⟨8931995179169309377489987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47637307622236316679946597 8931995179169309377489987)
          ·
            refine ⟨13397992768753964066234981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8931995179169309377489987 13397992768753964066234981)
            ·
              refine ⟨2512123644141368262419059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13397992768753964066234981 2512123644141368262419059)
              ·
                refine ⟨3768185466212052393628589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2512123644141368262419059 3768185466212052393628589)
                ·
                  refine ⟨1413069549829519647610721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3768185466212052393628589 1413069549829519647610721)
                  ·
                    refine ⟨1059802162372139735708041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1413069549829519647610721 1059802162372139735708041)
                    ·
                      refine ⟨794851621779104801781031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1059802162372139735708041 794851621779104801781031)
                      ·
                        rfl

theorem cell23_1547968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 1, 3, 2, 2].length) (baseStart_1547968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1547968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1547968 prefixEnd_1547968 := by exact prefixLift 1547968
  have htrace : WordTrace (prefixWord ++ tailWord_1547968) baseStart_1547968 baseEnd_1547968 := by
    simpa [prefixWord, tailWord_1547968, baseEnd_1547968] using wordTrace_append hprefix tailTrace_1547968
  have hstable : (prefixWord ++ tailWord_1547968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547968).length < 2 ^ (prefixWord ++ tailWord_1547968).sum := by decide
  have hdescent : baseEnd_1547968 < baseStart_1547968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547978 : List Nat := [3, 1, 2, 1, 6, 1, 1, 1, 1, 6]
def baseStart_1547978 : Nat := 118140960795 + 1547978 * 2 ^ 59
def prefixEnd_1547978 : Nat := 4983230072969 + 3 ^ 40 * 1547978 * 2
def baseEnd_1547978 : Nat := 264952252195216587551995

theorem tailTrace_1547978 : CollatzResearch.WordTrace tailWord_1547978 prefixEnd_1547978 264952252195216587551995 := by
  unfold tailWord_1547978
  simp only [CollatzResearch.WordTrace]
  refine ⟨14114848996486888609913147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37639597323965036293101725 14114848996486888609913147)
  ·
    refine ⟨21172273494730332914869721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14114848996486888609913147 21172273494730332914869721)
    ·
      refine ⟨15879205121047749686152291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21172273494730332914869721 15879205121047749686152291)
      ·
        refine ⟨23818807681571624529228437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15879205121047749686152291 23818807681571624529228437)
        ·
          refine ⟨1116506610073669899807583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23818807681571624529228437 1116506610073669899807583)
          ·
            refine ⟨1674759915110504849711375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1116506610073669899807583 1674759915110504849711375)
            ·
              refine ⟨2512139872665757274567063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1674759915110504849711375 2512139872665757274567063)
              ·
                refine ⟨3768209808998635911850595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2512139872665757274567063 3768209808998635911850595)
                ·
                  refine ⟨5652314713497953867775893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3768209808998635911850595 5652314713497953867775893)
                  ·
                    refine ⟨264952252195216587551995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5652314713497953867775893 264952252195216587551995)
                    ·
                      rfl

theorem cell23_1547978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 1, 1, 6].length) (baseStart_1547978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1547978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1547978 prefixEnd_1547978 := by exact prefixLift 1547978
  have htrace : WordTrace (prefixWord ++ tailWord_1547978) baseStart_1547978 baseEnd_1547978 := by
    simpa [prefixWord, tailWord_1547978, baseEnd_1547978] using wordTrace_append hprefix tailTrace_1547978
  have hstable : (prefixWord ++ tailWord_1547978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547978).length < 2 ^ (prefixWord ++ tailWord_1547978).sum := by decide
  have hdescent : baseEnd_1547978 < baseStart_1547978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547984 : List Nat := [2, 1, 1, 1, 1, 2, 1, 7, 1, 3, 3]
def baseStart_1547984 : Nat := 118140960795 + 1547984 * 2 ^ 59
def prefixEnd_1547984 : Nat := 4983230072969 + 3 ^ 40 * 1547984 * 2
def baseEnd_1547984 : Nat := 794859837469576739180957

theorem tailTrace_1547984 : CollatzResearch.WordTrace tailWord_1547984 prefixEnd_1547984 794859837469576739180957 := by
  unfold tailWord_1547984
  simp only [CollatzResearch.WordTrace]
  refine ⟨28229807411962908732185503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37639743215950544976247337 28229807411962908732185503)
  ·
    refine ⟨42344711117944363098278255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28229807411962908732185503 42344711117944363098278255)
    ·
      refine ⟨63517066676916544647417383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42344711117944363098278255 63517066676916544647417383)
      ·
        refine ⟨95275600015374816971126075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63517066676916544647417383 95275600015374816971126075)
        ·
          refine ⟨142913400023062225456689113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95275600015374816971126075 142913400023062225456689113)
          ·
            refine ⟨107185050017296669092516835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142913400023062225456689113 107185050017296669092516835)
            ·
              refine ⟨160777575025945003638775253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107185050017296669092516835 160777575025945003638775253)
              ·
                refine ⟨3768224414670586022783795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 160777575025945003638775253 3768224414670586022783795)
                ·
                  refine ⟨5652336622005879034175693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3768224414670586022783795 5652336622005879034175693)
                  ·
                    refine ⟨2119626233252204637815885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5652336622005879034175693 2119626233252204637815885)
                    ·
                      refine ⟨794859837469576739180957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2119626233252204637815885 794859837469576739180957)
                      ·
                        rfl

theorem cell23_1547984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3, 3].length) (baseStart_1547984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1547984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1547984 prefixEnd_1547984 := by exact prefixLift 1547984
  have htrace : WordTrace (prefixWord ++ tailWord_1547984) baseStart_1547984 baseEnd_1547984 := by
    simpa [prefixWord, tailWord_1547984, baseEnd_1547984] using wordTrace_append hprefix tailTrace_1547984
  have hstable : (prefixWord ++ tailWord_1547984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547984).length < 2 ^ (prefixWord ++ tailWord_1547984).sum := by decide
  have hdescent : baseEnd_1547984 < baseStart_1547984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547988 : List Nat := [2, 4, 1, 3, 1, 1, 1, 4, 1, 2, 3]
def baseStart_1547988 : Nat := 118140960795 + 1547988 * 2 ^ 59
def prefixEnd_1547988 : Nat := 4983230072969 + 3 ^ 40 * 1547988 * 2
def baseEnd_1547988 : Nat := 794861891392194723530939

theorem tailTrace_1547988 : CollatzResearch.WordTrace tailWord_1547988 prefixEnd_1547988 794861891392194723530939 := by
  unfold tailWord_1547988
  simp only [CollatzResearch.WordTrace]
  refine ⟨28229880357955663073758309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37639840477274217431677745 28229880357955663073758309)
  ·
    refine ⟨5293102567116686826329683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28229880357955663073758309 5293102567116686826329683)
    ·
      refine ⟨7939653850675030239494525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5293102567116686826329683 7939653850675030239494525)
      ·
        refine ⟨2977370194003136339810447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7939653850675030239494525 2977370194003136339810447)
        ·
          refine ⟨4466055291004704509715671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2977370194003136339810447 4466055291004704509715671)
          ·
            refine ⟨6699082936507056764573507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4466055291004704509715671 6699082936507056764573507)
            ·
              refine ⟨10048624404760585146860261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6699082936507056764573507 10048624404760585146860261)
              ·
                refine ⟨1884117075892609715036299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10048624404760585146860261 1884117075892609715036299)
                ·
                  refine ⟨2826175613838914572554449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1884117075892609715036299 2826175613838914572554449)
                  ·
                    refine ⟨2119631710379185929415837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2826175613838914572554449 2119631710379185929415837)
                    ·
                      refine ⟨794861891392194723530939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2119631710379185929415837 794861891392194723530939)
                      ·
                        rfl

theorem cell23_1547988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_1547988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1547988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1547988 prefixEnd_1547988 := by exact prefixLift 1547988
  have htrace : WordTrace (prefixWord ++ tailWord_1547988) baseStart_1547988 baseEnd_1547988 := by
    simpa [prefixWord, tailWord_1547988, baseEnd_1547988] using wordTrace_append hprefix tailTrace_1547988
  have hstable : (prefixWord ++ tailWord_1547988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547988).length < 2 ^ (prefixWord ++ tailWord_1547988).sum := by decide
  have hdescent : baseEnd_1547988 < baseStart_1547988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548014 : List Nat := [4, 1, 2, 1, 1, 2, 1, 2, 2, 2, 5]
def baseStart_1548014 : Nat := 118140960795 + 1548014 * 2 ^ 59
def prefixEnd_1548014 : Nat := 4983230072969 + 3 ^ 40 * 1548014 * 2
def baseEnd_1548014 : Nat := 794875241889211621805819

theorem tailTrace_1548014 : CollatzResearch.WordTrace tailWord_1548014 prefixEnd_1548014 794875241889211621805819 := by
  unfold tailWord_1548014
  simp only [CollatzResearch.WordTrace]
  refine ⟨7057588626727141573495387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37640472675878088391975397 7057588626727141573495387)
  ·
    refine ⟨10586382940090712360243081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7057588626727141573495387 10586382940090712360243081)
    ·
      refine ⟨7939787205068034270182311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10586382940090712360243081 7939787205068034270182311)
      ·
        refine ⟨11909680807602051405273467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7939787205068034270182311 11909680807602051405273467)
        ·
          refine ⟨17864521211403077107910201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11909680807602051405273467 17864521211403077107910201)
          ·
            refine ⟨13398390908552307830932651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17864521211403077107910201 13398390908552307830932651)
            ·
              refine ⟨20097586362828461746398977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13398390908552307830932651 20097586362828461746398977)
              ·
                refine ⟨15073189772121346309799233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20097586362828461746398977 15073189772121346309799233)
                ·
                  refine ⟨11304892329091009732349425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15073189772121346309799233 11304892329091009732349425)
                  ·
                    refine ⟨8478669246818257299262069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11304892329091009732349425 8478669246818257299262069)
                    ·
                      refine ⟨794875241889211621805819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8478669246818257299262069 794875241889211621805819)
                      ·
                        rfl

theorem cell23_1548014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_1548014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1548014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1548014 prefixEnd_1548014 := by exact prefixLift 1548014
  have htrace : WordTrace (prefixWord ++ tailWord_1548014) baseStart_1548014 baseEnd_1548014 := by
    simpa [prefixWord, tailWord_1548014, baseEnd_1548014] using wordTrace_append hprefix tailTrace_1548014
  have hstable : (prefixWord ++ tailWord_1548014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548014).length < 2 ^ (prefixWord ++ tailWord_1548014).sum := by decide
  have hdescent : baseEnd_1548014 < baseStart_1548014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548018 : List Nat := [3, 2, 1, 3, 1, 1, 2, 4, 2, 1, 3]
def baseStart_1548018 : Nat := 118140960795 + 1548018 * 2 ^ 59
def prefixEnd_1548018 : Nat := 4983230072969 + 3 ^ 40 * 1548018 * 2
def baseEnd_1548018 : Nat := 794877295811829606155801

theorem tailTrace_1548018 : CollatzResearch.WordTrace tailWord_1548018 prefixEnd_1548018 794877295811829606155801 := by
  unfold tailWord_1548018
  simp only [CollatzResearch.WordTrace]
  refine ⟨14115213726450660317777177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37640569937201760847405805 14115213726450660317777177)
  ·
    refine ⟨10586410294837995238332883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14115213726450660317777177 10586410294837995238332883)
    ·
      refine ⟨15879615442256992857499325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10586410294837995238332883 15879615442256992857499325)
      ·
        refine ⟨5954855790846372321562247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15879615442256992857499325 5954855790846372321562247)
        ·
          refine ⟨8932283686269558482343371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5954855790846372321562247 8932283686269558482343371)
          ·
            refine ⟨13398425529404337723515057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8932283686269558482343371 13398425529404337723515057)
            ·
              refine ⟨10048819147053253292636293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13398425529404337723515057 10048819147053253292636293)
              ·
                refine ⟨1884153590072484992369305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10048819147053253292636293 1884153590072484992369305)
                ·
                  refine ⟨1413115192554363744276979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1884153590072484992369305 1413115192554363744276979)
                  ·
                    refine ⟨2119672788831545616415469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1413115192554363744276979 2119672788831545616415469)
                    ·
                      refine ⟨794877295811829606155801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2119672788831545616415469 794877295811829606155801)
                      ·
                        rfl

theorem cell23_1548018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_1548018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1548018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1548018 prefixEnd_1548018 := by exact prefixLift 1548018
  have htrace : WordTrace (prefixWord ++ tailWord_1548018) baseStart_1548018 baseEnd_1548018 := by
    simpa [prefixWord, tailWord_1548018, baseEnd_1548018] using wordTrace_append hprefix tailTrace_1548018
  have hstable : (prefixWord ++ tailWord_1548018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548018).length < 2 ^ (prefixWord ++ tailWord_1548018).sum := by decide
  have hdescent : baseEnd_1548018 < baseStart_1548018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548041 : List Nat := [1, 2, 1, 1, 3, 2, 1, 5, 1, 4, 2]
def baseStart_1548041 : Nat := 118140960795 + 1548041 * 2 ^ 59
def prefixEnd_1548041 : Nat := 4983230072969 + 3 ^ 40 * 1548041 * 2
def baseEnd_1548041 : Nat := 794889105866883016168195

theorem tailTrace_1548041 : CollatzResearch.WordTrace tailWord_1548041 prefixEnd_1548041 794889105866883016168195 := by
  unfold tailWord_1548041
  simp only [CollatzResearch.WordTrace]
  refine ⟨56461693784719316199195977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37641129189812877466130651 56461693784719316199195977)
  ·
    refine ⟨42346270338539487149396983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56461693784719316199195977 42346270338539487149396983)
    ·
      refine ⟨63519405507809230724095475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42346270338539487149396983 63519405507809230724095475)
      ·
        refine ⟨95279108261713846086143213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63519405507809230724095475 95279108261713846086143213)
        ·
          refine ⟨35729665598142692282303705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95279108261713846086143213 35729665598142692282303705)
          ·
            refine ⟨26797249198607019211727779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35729665598142692282303705 26797249198607019211727779)
            ·
              refine ⟨40195873797910528817591669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26797249198607019211727779 40195873797910528817591669)
              ·
                refine ⟨3768363168554112076649219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40195873797910528817591669 3768363168554112076649219)
                ·
                  refine ⟨5652544752831168114973829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3768363168554112076649219 5652544752831168114973829)
                  ·
                    refine ⟨1059852141155844021557593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5652544752831168114973829 1059852141155844021557593)
                    ·
                      refine ⟨794889105866883016168195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1059852141155844021557593 794889105866883016168195)
                      ·
                        rfl

theorem cell23_1548041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 1, 4, 2].length) (baseStart_1548041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1548041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1548041 prefixEnd_1548041 := by exact prefixLift 1548041
  have htrace : WordTrace (prefixWord ++ tailWord_1548041) baseStart_1548041 baseEnd_1548041 := by
    simpa [prefixWord, tailWord_1548041, baseEnd_1548041] using wordTrace_append hprefix tailTrace_1548041
  have hstable : (prefixWord ++ tailWord_1548041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548041).length < 2 ^ (prefixWord ++ tailWord_1548041).sum := by decide
  have hdescent : baseEnd_1548041 < baseStart_1548041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548044 : List Nat := [2, 2, 1, 2, 2, 1, 3, 2, 2, 1, 5]
def baseStart_1548044 : Nat := 118140960795 + 1548044 * 2 ^ 59
def prefixEnd_1548044 : Nat := 4983230072969 + 3 ^ 40 * 1548044 * 2
def baseEnd_1548044 : Nat := 794890646308846504430681

theorem tailTrace_1548044 : CollatzResearch.WordTrace tailWord_1548044 prefixEnd_1548044 794890646308846504430681 := by
  unfold tailWord_1548044
  simp only [CollatzResearch.WordTrace]
  refine ⟨28230901601854223855777593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37641202135805631807703457 28230901601854223855777593)
  ·
    refine ⟨21173176201390667891833195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28230901601854223855777593 21173176201390667891833195)
    ·
      refine ⟨31759764302086001837749793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21173176201390667891833195 31759764302086001837749793)
      ·
        refine ⟨23819823226564501378312345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31759764302086001837749793 23819823226564501378312345)
        ·
          refine ⟨17864867419923376033734259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23819823226564501378312345 17864867419923376033734259)
          ·
            refine ⟨26797301129885064050601389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17864867419923376033734259 26797301129885064050601389)
            ·
              refine ⟨10048987923706899018975521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26797301129885064050601389 10048987923706899018975521)
              ·
                refine ⟨7536740942780174264231641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10048987923706899018975521 7536740942780174264231641)
                ·
                  refine ⟨5652555707085130698173731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7536740942780174264231641 5652555707085130698173731)
                  ·
                    refine ⟨8478833560627696047260597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5652555707085130698173731 8478833560627696047260597)
                    ·
                      refine ⟨794890646308846504430681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8478833560627696047260597 794890646308846504430681)
                      ·
                        rfl

theorem cell23_1548044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_1548044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1548044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1548044 prefixEnd_1548044 := by exact prefixLift 1548044
  have htrace : WordTrace (prefixWord ++ tailWord_1548044) baseStart_1548044 baseEnd_1548044 := by
    simpa [prefixWord, tailWord_1548044, baseEnd_1548044] using wordTrace_append hprefix tailTrace_1548044
  have hstable : (prefixWord ++ tailWord_1548044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548044).length < 2 ^ (prefixWord ++ tailWord_1548044).sum := by decide
  have hdescent : baseEnd_1548044 < baseStart_1548044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548052 : List Nat := [2, 4, 4, 1, 1, 1, 1, 2, 1, 3, 3]
def baseStart_1548052 : Nat := 118140960795 + 1548052 * 2 ^ 59
def prefixEnd_1548052 : Nat := 4983230072969 + 3 ^ 40 * 1548052 * 2
def baseEnd_1548052 : Nat := 794894754154082473130645

theorem tailTrace_1548052 : CollatzResearch.WordTrace tailWord_1548052 prefixEnd_1548052 794894754154082473130645 := by
  unfold tailWord_1548052
  simp only [CollatzResearch.WordTrace]
  refine ⟨28231047493839732538923205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37641396658452976718564273 28231047493839732538923205)
  ·
    refine ⟨5293321405094949851048101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28231047493839732538923205 5293321405094949851048101)
    ·
      refine ⟨992497763455303097071519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5293321405094949851048101 992497763455303097071519)
      ·
        refine ⟨1488746645182954645607279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 992497763455303097071519 1488746645182954645607279)
        ·
          refine ⟨2233119967774431968410919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1488746645182954645607279 2233119967774431968410919)
          ·
            refine ⟨3349679951661647952616379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2233119967774431968410919 3349679951661647952616379)
            ·
              refine ⟨5024519927492471928924569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3349679951661647952616379 5024519927492471928924569)
              ·
                refine ⟨3768389945619353946693427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5024519927492471928924569 3768389945619353946693427)
                ·
                  refine ⟨5652584918429030920040141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3768389945619353946693427 5652584918429030920040141)
                  ·
                    refine ⟨2119719344410886595015053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5652584918429030920040141 2119719344410886595015053)
                    ·
                      refine ⟨794894754154082473130645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2119719344410886595015053 794894754154082473130645)
                      ·
                        rfl

theorem cell23_1548052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_1548052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1548052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1548052 prefixEnd_1548052 := by exact prefixLift 1548052
  have htrace : WordTrace (prefixWord ++ tailWord_1548052) baseStart_1548052 baseEnd_1548052 := by
    simpa [prefixWord, tailWord_1548052, baseEnd_1548052] using wordTrace_append hprefix tailTrace_1548052
  have hstable : (prefixWord ++ tailWord_1548052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548052).length < 2 ^ (prefixWord ++ tailWord_1548052).sum := by decide
  have hdescent : baseEnd_1548052 < baseStart_1548052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548058 : List Nat := [3, 1, 1, 3, 2, 3, 1, 2, 1, 4, 2]
def baseStart_1548058 : Nat := 118140960795 + 1548058 * 2 ^ 59
def prefixEnd_1548058 : Nat := 4983230072969 + 3 ^ 40 * 1548058 * 2
def baseEnd_1548058 : Nat := 794897835038009449655617

theorem tailTrace_1548058 : CollatzResearch.WordTrace tailWord_1548058 prefixEnd_1548058 794897835038009449655617 := by
  unfold tailWord_1548058
  simp only [CollatzResearch.WordTrace]
  refine ⟨14115578456414432025641207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37641542550438485401709885 14115578456414432025641207)
  ·
    refine ⟨21173367684621648038461811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14115578456414432025641207 21173367684621648038461811)
    ·
      refine ⟨31760051526932472057692717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21173367684621648038461811 31760051526932472057692717)
      ·
        refine ⟨11910019322599677021634769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31760051526932472057692717 11910019322599677021634769)
        ·
          refine ⟨8932514491949757766226077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11910019322599677021634769 8932514491949757766226077)
          ·
            refine ⟨3349692934481159162334779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8932514491949757766226077 3349692934481159162334779)
            ·
              refine ⟨5024539401721738743502169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3349692934481159162334779 5024539401721738743502169)
              ·
                refine ⟨3768404551291304057626627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5024539401721738743502169 3768404551291304057626627)
                ·
                  refine ⟨5652606826936956086439941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3768404551291304057626627 5652606826936956086439941)
                  ·
                    refine ⟨1059863780050679266207489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5652606826936956086439941 1059863780050679266207489)
                    ·
                      refine ⟨794897835038009449655617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1059863780050679266207489 794897835038009449655617)
                      ·
                        rfl

theorem cell23_1548058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 2, 1, 4, 2].length) (baseStart_1548058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1548058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1548058 prefixEnd_1548058 := by exact prefixLift 1548058
  have htrace : WordTrace (prefixWord ++ tailWord_1548058) baseStart_1548058 baseEnd_1548058 := by
    simpa [prefixWord, tailWord_1548058, baseEnd_1548058] using wordTrace_append hprefix tailTrace_1548058
  have hstable : (prefixWord ++ tailWord_1548058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548058).length < 2 ^ (prefixWord ++ tailWord_1548058).sum := by decide
  have hdescent : baseEnd_1548058 < baseStart_1548058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548101 : List Nat := [1, 3, 1, 1, 1, 2, 3, 2, 2, 5, 2]
def baseStart_1548101 : Nat := 118140960795 + 1548101 * 2 ^ 59
def prefixEnd_1548101 : Nat := 4983230072969 + 3 ^ 40 * 1548101 * 2
def baseEnd_1548101 : Nat := 794919914706152781417919

theorem tailTrace_1548101 : CollatzResearch.WordTrace tailWord_1548101 prefixEnd_1548101 794919914706152781417919 := by
  unfold tailWord_1548101
  simp only [CollatzResearch.WordTrace]
  refine ⟨56463882164501946446380157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37642588109667964297586771 56463882164501946446380157)
  ·
    refine ⟨21173955811688229917392559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56463882164501946446380157 21173955811688229917392559)
    ·
      refine ⟨31760933717532344876088839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21173955811688229917392559 31760933717532344876088839)
      ·
        refine ⟨47641400576298517314133259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31760933717532344876088839 47641400576298517314133259)
        ·
          refine ⟨71462100864447775971199889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47641400576298517314133259 71462100864447775971199889)
          ·
            refine ⟨53596575648335831978399917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71462100864447775971199889 53596575648335831978399917)
            ·
              refine ⟨20098715868125936991899969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53596575648335831978399917 20098715868125936991899969)
              ·
                refine ⟨15074036901094452743924977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20098715868125936991899969 15074036901094452743924977)
                ·
                  refine ⟨11305527675820839557943733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15074036901094452743924977 11305527675820839557943733)
                  ·
                    refine ⟨1059893219608203708557225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11305527675820839557943733 1059893219608203708557225)
                    ·
                      refine ⟨794919914706152781417919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1059893219608203708557225 794919914706152781417919)
                      ·
                        rfl

theorem cell23_1548101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 5, 2].length) (baseStart_1548101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1548101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1548101 prefixEnd_1548101 := by exact prefixLift 1548101
  have htrace : WordTrace (prefixWord ++ tailWord_1548101) baseStart_1548101 baseEnd_1548101 := by
    simpa [prefixWord, tailWord_1548101, baseEnd_1548101] using wordTrace_append hprefix tailTrace_1548101
  have hstable : (prefixWord ++ tailWord_1548101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548101).length < 2 ^ (prefixWord ++ tailWord_1548101).sum := by decide
  have hdescent : baseEnd_1548101 < baseStart_1548101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548144 : List Nat := [2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 6]
def baseStart_1548144 : Nat := 118140960795 + 1548144 * 2 ^ 59
def prefixEnd_1548144 : Nat := 4983230072969 + 3 ^ 40 * 1548144 * 2
def baseEnd_1548144 : Nat := 794941994374296113180221

theorem tailTrace_1548144 : CollatzResearch.WordTrace tailWord_1548144 prefixEnd_1548144 794941994374296113180221 := by
  unfold tailWord_1548144
  simp only [CollatzResearch.WordTrace]
  refine ⟨28232725251673082395097743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37643633668897443193463657 28232725251673082395097743)
  ·
    refine ⟨42349087877509623592646615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28232725251673082395097743 42349087877509623592646615)
    ·
      refine ⟨63523631816264435388969923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42349087877509623592646615 63523631816264435388969923)
      ·
        refine ⟨95285447724396653083454885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63523631816264435388969923 95285447724396653083454885)
        ·
          refine ⟨17866021448324372453147791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95285447724396653083454885 17866021448324372453147791)
          ·
            refine ⟨26799032172486558679721687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17866021448324372453147791 26799032172486558679721687)
            ·
              refine ⟨40198548258729838019582531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26799032172486558679721687 40198548258729838019582531)
              ·
                refine ⟨60297822388094757029373797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40198548258729838019582531 60297822388094757029373797)
                ·
                  refine ⟨11305841697767766943007587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60297822388094757029373797 11305841697767766943007587)
                  ·
                    refine ⟨16958762546651650414511381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11305841697767766943007587 16958762546651650414511381)
                    ·
                      refine ⟨794941994374296113180221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16958762546651650414511381 794941994374296113180221)
                      ·
                        rfl

theorem cell23_1548144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 6].length) (baseStart_1548144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1548144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1548144 prefixEnd_1548144 := by exact prefixLift 1548144
  have htrace : WordTrace (prefixWord ++ tailWord_1548144) baseStart_1548144 baseEnd_1548144 := by
    simpa [prefixWord, tailWord_1548144, baseEnd_1548144] using wordTrace_append hprefix tailTrace_1548144
  have hstable : (prefixWord ++ tailWord_1548144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548144).length < 2 ^ (prefixWord ++ tailWord_1548144).sum := by decide
  have hdescent : baseEnd_1548144 < baseStart_1548144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548241 : List Nat := [1, 2, 2, 1, 2, 1, 2, 5, 1, 1, 5]
def baseStart_1548241 : Nat := 118140960795 + 1548241 * 2 ^ 59
def prefixEnd_1548241 : Nat := 4983230072969 + 3 ^ 40 * 1548241 * 2
def baseEnd_1548241 : Nat := 794991801997782233667275

theorem tailTrace_1548241 : CollatzResearch.WordTrace tailWord_1548241 prefixEnd_1548241 794991801997782233667275 := by
  unfold tailWord_1548241
  simp only [CollatzResearch.WordTrace]
  refine ⟨56468988383994750356476577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37645992255996500237651051 56468988383994750356476577)
  ·
    refine ⟨42351741287996062767357433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56468988383994750356476577 42351741287996062767357433)
    ·
      refine ⟨31763805965997047075518075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42351741287996062767357433 31763805965997047075518075)
      ·
        refine ⟨47645708948995570613277113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31763805965997047075518075 47645708948995570613277113)
        ·
          refine ⟨35734281711746677959957835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47645708948995570613277113 35734281711746677959957835)
          ·
            refine ⟨53601422567620016939936753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35734281711746677959957835 53601422567620016939936753)
            ·
              refine ⟨40201066925715012704952565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53601422567620016939936753 40201066925715012704952565)
              ·
                refine ⟨3768850024285782441089303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40201066925715012704952565 3768850024285782441089303)
                ·
                  refine ⟨5653275036428673661633955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3768850024285782441089303 5653275036428673661633955)
                  ·
                    refine ⟨8479912554643010492450933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5653275036428673661633955 8479912554643010492450933)
                    ·
                      refine ⟨794991801997782233667275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8479912554643010492450933 794991801997782233667275)
                      ·
                        rfl

theorem cell23_1548241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5, 1, 1, 5].length) (baseStart_1548241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1548241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1548241 prefixEnd_1548241 := by exact prefixLift 1548241
  have htrace : WordTrace (prefixWord ++ tailWord_1548241) baseStart_1548241 baseEnd_1548241 := by
    simpa [prefixWord, tailWord_1548241, baseEnd_1548241] using wordTrace_append hprefix tailTrace_1548241
  have hstable : (prefixWord ++ tailWord_1548241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548241).length < 2 ^ (prefixWord ++ tailWord_1548241).sum := by decide
  have hdescent : baseEnd_1548241 < baseStart_1548241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548289 : List Nat := [1, 2, 4, 1, 2, 1, 4, 3, 1, 2, 2]
def baseStart_1548289 : Nat := 118140960795 + 1548289 * 2 ^ 59
def prefixEnd_1548289 : Nat := 4983230072969 + 3 ^ 40 * 1548289 * 2
def baseEnd_1548289 : Nat := 795016449069198045867055

theorem tailTrace_1548289 : CollatzResearch.WordTrace tailWord_1548289 prefixEnd_1548289 795016449069198045867055 := by
  unfold tailWord_1548289
  simp only [CollatzResearch.WordTrace]
  refine ⟨56470739087820854554223921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37647159391880569702815947 56470739087820854554223921)
  ·
    refine ⟨42353054315865640915667941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56470739087820854554223921 42353054315865640915667941)
    ·
      refine ⟨7941197684224807671687739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42353054315865640915667941 7941197684224807671687739)
      ·
        refine ⟨11911796526337211507531609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7941197684224807671687739 11911796526337211507531609)
        ·
          refine ⟨8933847394752908630648707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11911796526337211507531609 8933847394752908630648707)
          ·
            refine ⟨13400771092129362945973061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8933847394752908630648707 13400771092129362945973061)
            ·
              refine ⟨2512644579774255552369949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13400771092129362945973061 2512644579774255552369949)
              ·
                refine ⟨942241717415345832138731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2512644579774255552369949 942241717415345832138731)
                ·
                  refine ⟨1413362576123018748208097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 942241717415345832138731 1413362576123018748208097)
                  ·
                    refine ⟨1060021932092264061156073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1413362576123018748208097 1060021932092264061156073)
                    ·
                      refine ⟨795016449069198045867055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1060021932092264061156073 795016449069198045867055)
                      ·
                        rfl

theorem cell23_1548289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 3, 1, 2, 2].length) (baseStart_1548289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1548289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1548289 prefixEnd_1548289 := by exact prefixLift 1548289
  have htrace : WordTrace (prefixWord ++ tailWord_1548289) baseStart_1548289 baseEnd_1548289 := by
    simpa [prefixWord, tailWord_1548289, baseEnd_1548289] using wordTrace_append hprefix tailTrace_1548289
  have hstable : (prefixWord ++ tailWord_1548289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548289).length < 2 ^ (prefixWord ++ tailWord_1548289).sum := by decide
  have hdescent : baseEnd_1548289 < baseStart_1548289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548340 : List Nat := [2, 5, 1, 2, 3, 1, 1, 3, 1, 2, 2]
def baseStart_1548340 : Nat := 118140960795 + 1548340 * 2 ^ 59
def prefixEnd_1548340 : Nat := 4983230072969 + 3 ^ 40 * 1548340 * 2
def baseEnd_1548340 : Nat := 795042636582577346329321

theorem tailTrace_1548340 : CollatzResearch.WordTrace tailWord_1548340 prefixEnd_1548340 795042636582577346329321 := by
  unfold tailWord_1548340
  simp only [CollatzResearch.WordTrace]
  refine ⟨28236299605318045132165237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37648399473757393509553649 28236299605318045132165237)
  ·
    refine ⟨2647153087998566731140491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28236299605318045132165237 2647153087998566731140491)
    ·
      refine ⟨3970729631997850096710737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2647153087998566731140491 3970729631997850096710737)
      ·
        refine ⟨2978047223998387572533053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3970729631997850096710737 2978047223998387572533053)
        ·
          refine ⟨1116767708999395339699895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2978047223998387572533053 1116767708999395339699895)
          ·
            refine ⟨1675151563499093009549843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1116767708999395339699895 1675151563499093009549843)
            ·
              refine ⟨2512727345248639514324765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1675151563499093009549843 2512727345248639514324765)
              ·
                refine ⟨942272754468239817871787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2512727345248639514324765 942272754468239817871787)
                ·
                  refine ⟨1413409131702359726807681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 942272754468239817871787 1413409131702359726807681)
                  ·
                    refine ⟨1060056848776769795105761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1413409131702359726807681 1060056848776769795105761)
                    ·
                      refine ⟨795042636582577346329321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1060056848776769795105761 795042636582577346329321)
                      ·
                        rfl

theorem cell23_1548340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_1548340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1548340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1548340 prefixEnd_1548340 := by exact prefixLift 1548340
  have htrace : WordTrace (prefixWord ++ tailWord_1548340) baseStart_1548340 baseEnd_1548340 := by
    simpa [prefixWord, tailWord_1548340, baseEnd_1548340] using wordTrace_append hprefix tailTrace_1548340
  have hstable : (prefixWord ++ tailWord_1548340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548340).length < 2 ^ (prefixWord ++ tailWord_1548340).sum := by decide
  have hdescent : baseEnd_1548340 < baseStart_1548340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548348 : List Nat := [2, 2, 2, 2, 2, 1, 3, 1, 2, 1, 5]
def baseStart_1548348 : Nat := 118140960795 + 1548348 * 2 ^ 59
def prefixEnd_1548348 : Nat := 4983230072969 + 3 ^ 40 * 1548348 * 2
def baseEnd_1548348 : Nat := 795046744427813315029283

theorem tailTrace_1548348 : CollatzResearch.WordTrace tailWord_1548348 prefixEnd_1548348 795046744427813315029283 := by
  unfold tailWord_1548348
  simp only [CollatzResearch.WordTrace]
  refine ⟨28236445497303553815310849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37648593996404738420414465 28236445497303553815310849)
  ·
    refine ⟨21177334122977665361483137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28236445497303553815310849 21177334122977665361483137)
    ·
      refine ⟨15883000592233249021112353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21177334122977665361483137 15883000592233249021112353)
      ·
        refine ⟨11912250444174936765834265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15883000592233249021112353 11912250444174936765834265)
        ·
          refine ⟨8934187833131202574375699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11912250444174936765834265 8934187833131202574375699)
          ·
            refine ⟨13401281749696803861563549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8934187833131202574375699 13401281749696803861563549)
            ·
              refine ⟨5025480656136301448086331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13401281749696803861563549 5025480656136301448086331)
              ·
                refine ⟨7538220984204452172129497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5025480656136301448086331 7538220984204452172129497)
                ·
                  refine ⟨5653665738153339129097123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7538220984204452172129497 5653665738153339129097123)
                  ·
                    refine ⟨8480498607230008693645685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5653665738153339129097123 8480498607230008693645685)
                    ·
                      refine ⟨795046744427813315029283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8480498607230008693645685 795046744427813315029283)
                      ·
                        rfl

theorem cell23_1548348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_1548348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1548348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1548348 prefixEnd_1548348 := by exact prefixLift 1548348
  have htrace : WordTrace (prefixWord ++ tailWord_1548348) baseStart_1548348 baseEnd_1548348 := by
    simpa [prefixWord, tailWord_1548348, baseEnd_1548348] using wordTrace_append hprefix tailTrace_1548348
  have hstable : (prefixWord ++ tailWord_1548348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548348).length < 2 ^ (prefixWord ++ tailWord_1548348).sum := by decide
  have hdescent : baseEnd_1548348 < baseStart_1548348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548351 : List Nat := [1, 1, 2, 2, 3, 1, 2, 2, 9]
def baseStart_1548351 : Nat := 118140960795 + 1548351 * 2 ^ 59
def prefixEnd_1548351 : Nat := 4983230072969 + 3 ^ 40 * 1548351 * 2
def baseEnd_1548351 : Nat := 88338698318864089254641

theorem tailTrace_1548351 : CollatzResearch.WordTrace tailWord_1548351 prefixEnd_1548351 88338698318864089254641 := by
  unfold tailWord_1548351
  simp only [CollatzResearch.WordTrace]
  refine ⟨56473000413596239142980907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37648666942397492761987271 56473000413596239142980907)
  ·
    refine ⟨84709500620394358714471361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56473000413596239142980907 84709500620394358714471361)
    ·
      refine ⟨63532125465295769035853521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84709500620394358714471361 63532125465295769035853521)
      ·
        refine ⟨47649094098971826776890141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63532125465295769035853521 47649094098971826776890141)
        ·
          refine ⟨17868410287114435041333803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47649094098971826776890141 17868410287114435041333803)
          ·
            refine ⟨26802615430671652562000705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17868410287114435041333803 26802615430671652562000705)
            ·
              refine ⟨20101961573003739421500529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26802615430671652562000705 20101961573003739421500529)
              ·
                refine ⟨15076471179752804566125397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20101961573003739421500529 15076471179752804566125397)
                ·
                  refine ⟨88338698318864089254641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 15076471179752804566125397 88338698318864089254641)
                  ·
                    rfl

theorem cell23_1548351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 9].length) (baseStart_1548351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1548351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1548351 prefixEnd_1548351 := by exact prefixLift 1548351
  have htrace : WordTrace (prefixWord ++ tailWord_1548351) baseStart_1548351 baseEnd_1548351 := by
    simpa [prefixWord, tailWord_1548351, baseEnd_1548351] using wordTrace_append hprefix tailTrace_1548351
  have hstable : (prefixWord ++ tailWord_1548351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548351).length < 2 ^ (prefixWord ++ tailWord_1548351).sum := by decide
  have hdescent : baseEnd_1548351 < baseStart_1548351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548361 : List Nat := [1, 2, 1, 1, 2, 2, 3, 1, 1, 2, 7]
def baseStart_1548361 : Nat := 118140960795 + 1548361 * 2 ^ 59
def prefixEnd_1548361 : Nat := 4983230072969 + 3 ^ 40 * 1548361 * 2
def baseEnd_1548361 : Nat := 795053419676321764166723

theorem tailTrace_1548361 : CollatzResearch.WordTrace tailWord_1548361 prefixEnd_1548361 795053419676321764166723 := by
  unfold tailWord_1548361
  simp only [CollatzResearch.WordTrace]
  refine ⟨56473365143560010850844937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37648910095706673900563291 56473365143560010850844937)
  ·
    refine ⟨42355023857670008138133703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56473365143560010850844937 42355023857670008138133703)
    ·
      refine ⟨63532535786505012207200555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42355023857670008138133703 63532535786505012207200555)
      ·
        refine ⟨95298803679757518310800833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63532535786505012207200555 95298803679757518310800833)
        ·
          refine ⟨71474102759818138733100625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95298803679757518310800833 71474102759818138733100625)
          ·
            refine ⟨53605577069863604049825469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71474102759818138733100625 53605577069863604049825469)
            ·
              refine ⟨20102091401198851518684551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53605577069863604049825469 20102091401198851518684551)
              ·
                refine ⟨30153137101798277278026827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20102091401198851518684551 30153137101798277278026827)
                ·
                  refine ⟨45229705652697415917040241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30153137101798277278026827 45229705652697415917040241)
                  ·
                    refine ⟨33922279239523061937780181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45229705652697415917040241 33922279239523061937780181)
                    ·
                      refine ⟨795053419676321764166723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 33922279239523061937780181 795053419676321764166723)
                      ·
                        rfl

theorem cell23_1548361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 2, 7].length) (baseStart_1548361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1548361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1548361 prefixEnd_1548361 := by exact prefixLift 1548361
  have htrace : WordTrace (prefixWord ++ tailWord_1548361) baseStart_1548361 baseEnd_1548361 := by
    simpa [prefixWord, tailWord_1548361, baseEnd_1548361] using wordTrace_append hprefix tailTrace_1548361
  have hstable : (prefixWord ++ tailWord_1548361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548361).length < 2 ^ (prefixWord ++ tailWord_1548361).sum := by decide
  have hdescent : baseEnd_1548361 < baseStart_1548361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548362 : List Nat := [3, 1, 2, 1, 1, 2, 1, 6, 2, 2, 2]
def baseStart_1548362 : Nat := 118140960795 + 1548362 * 2 ^ 59
def prefixEnd_1548362 : Nat := 4983230072969 + 3 ^ 40 * 1548362 * 2
def baseEnd_1548362 : Nat := 795053933156976260254219

theorem tailTrace_1548362 : CollatzResearch.WordTrace tailWord_1548362 prefixEnd_1548362 795053933156976260254219 := by
  unfold tailWord_1548362
  simp only [CollatzResearch.WordTrace]
  refine ⟨14118350404139097005407835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37648934411037592014420893 14118350404139097005407835)
  ·
    refine ⟨21177525606208645508111753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14118350404139097005407835 21177525606208645508111753)
    ·
      refine ⟨15883144204656484131083815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21177525606208645508111753 15883144204656484131083815)
      ·
        refine ⟨23824716306984726196625723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15883144204656484131083815 23824716306984726196625723)
        ·
          refine ⟨35737074460477089294938585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23824716306984726196625723 35737074460477089294938585)
          ·
            refine ⟨26802805845357816971203939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35737074460477089294938585 26802805845357816971203939)
            ·
              refine ⟨40204208768036725456805909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26802805845357816971203939 40204208768036725456805909)
              ·
                refine ⟨1884572286001721505787777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40204208768036725456805909 1884572286001721505787777)
                ·
                  refine ⟨1413429214501291129340833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1884572286001721505787777 1413429214501291129340833)
                  ·
                    refine ⟨1060071910875968347005625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1413429214501291129340833 1060071910875968347005625)
                    ·
                      refine ⟨795053933156976260254219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1060071910875968347005625 795053933156976260254219)
                      ·
                        rfl

theorem cell23_1548362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 6, 2, 2, 2].length) (baseStart_1548362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1548362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1548362 prefixEnd_1548362 := by exact prefixLift 1548362
  have htrace : WordTrace (prefixWord ++ tailWord_1548362) baseStart_1548362 baseEnd_1548362 := by
    simpa [prefixWord, tailWord_1548362, baseEnd_1548362] using wordTrace_append hprefix tailTrace_1548362
  have hstable : (prefixWord ++ tailWord_1548362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548362).length < 2 ^ (prefixWord ++ tailWord_1548362).sum := by decide
  have hdescent : baseEnd_1548362 < baseStart_1548362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548365 : List Nat := [1, 6, 1, 1, 1, 1, 2, 1, 2, 4, 3]
def baseStart_1548365 : Nat := 118140960795 + 1548365 * 2 ^ 59
def prefixEnd_1548365 : Nat := 4983230072969 + 3 ^ 40 * 1548365 * 2
def baseEnd_1548365 : Nat := 795055473598939748516705

theorem tailTrace_1548365 : CollatzResearch.WordTrace tailWord_1548365 prefixEnd_1548365 795055473598939748516705 := by
  unfold tailWord_1548365
  simp only [CollatzResearch.WordTrace]
  refine ⟨56473511035545519533990549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37649007357030346355993699 56473511035545519533990549)
  ·
    refine ⟨2647195829791196228155807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 56473511035545519533990549 2647195829791196228155807)
    ·
      refine ⟨3970793744686794342233711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2647195829791196228155807 3970793744686794342233711)
      ·
        refine ⟨5956190617030191513350567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3970793744686794342233711 5956190617030191513350567)
        ·
          refine ⟨8934285925545287270025851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5956190617030191513350567 8934285925545287270025851)
          ·
            refine ⟨13401428888317930905038777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8934285925545287270025851 13401428888317930905038777)
            ·
              refine ⟨10051071666238448178779083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13401428888317930905038777 10051071666238448178779083)
              ·
                refine ⟨15076607499357672268168625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10051071666238448178779083 15076607499357672268168625)
                ·
                  refine ⟨11307455624518254201126469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15076607499357672268168625 11307455624518254201126469)
                  ·
                    refine ⟨2120147929597172662711213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11307455624518254201126469 2120147929597172662711213)
                    ·
                      refine ⟨795055473598939748516705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2120147929597172662711213 795055473598939748516705)
                      ·
                        rfl

theorem cell23_1548365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_1548365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1548365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1548365 prefixEnd_1548365 := by exact prefixLift 1548365
  have htrace : WordTrace (prefixWord ++ tailWord_1548365) baseStart_1548365 baseEnd_1548365 := by
    simpa [prefixWord, tailWord_1548365, baseEnd_1548365] using wordTrace_append hprefix tailTrace_1548365
  have hstable : (prefixWord ++ tailWord_1548365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548365).length < 2 ^ (prefixWord ++ tailWord_1548365).sum := by decide
  have hdescent : baseEnd_1548365 < baseStart_1548365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548378 : List Nat := [3, 1, 1, 2, 1, 1, 4, 1, 1, 5, 3]
def baseStart_1548378 : Nat := 118140960795 + 1548378 * 2 ^ 59
def prefixEnd_1548378 : Nat := 4983230072969 + 3 ^ 40 * 1548378 * 2
def baseEnd_1548378 : Nat := 795062148847448197654145

theorem tailTrace_1548378 : CollatzResearch.WordTrace tailWord_1548378 prefixEnd_1548378 795062148847448197654145 := by
  unfold tailWord_1548378
  simp only [CollatzResearch.WordTrace]
  refine ⟨14118496296124605688553447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37649323456332281836142525 14118496296124605688553447)
  ·
    refine ⟨21177744444186908532830171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14118496296124605688553447 21177744444186908532830171)
    ·
      refine ⟨31766616666280362799245257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21177744444186908532830171 31766616666280362799245257)
      ·
        refine ⟨23824962499710272099433943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31766616666280362799245257 23824962499710272099433943)
        ·
          refine ⟨35737443749565408149150915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23824962499710272099433943 35737443749565408149150915)
          ·
            refine ⟨53606165624348112223726373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35737443749565408149150915 53606165624348112223726373)
            ·
              refine ⟨10051156054565271041948695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53606165624348112223726373 10051156054565271041948695)
              ·
                refine ⟨15076734081847906562923043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10051156054565271041948695 15076734081847906562923043)
                ·
                  refine ⟨22615101122771859844384565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15076734081847906562923043 22615101122771859844384565)
                  ·
                    refine ⟨2120165730259861860411053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22615101122771859844384565 2120165730259861860411053)
                    ·
                      refine ⟨795062148847448197654145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2120165730259861860411053 795062148847448197654145)
                      ·
                        rfl

theorem cell23_1548378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 1, 5, 3].length) (baseStart_1548378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1548378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1548378 prefixEnd_1548378 := by exact prefixLift 1548378
  have htrace : WordTrace (prefixWord ++ tailWord_1548378) baseStart_1548378 baseEnd_1548378 := by
    simpa [prefixWord, tailWord_1548378, baseEnd_1548378] using wordTrace_append hprefix tailTrace_1548378
  have hstable : (prefixWord ++ tailWord_1548378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548378).length < 2 ^ (prefixWord ++ tailWord_1548378).sum := by decide
  have hdescent : baseEnd_1548378 < baseStart_1548378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548445 : List Nat := [1, 4, 2, 1, 1, 3, 1, 1, 5, 4]
def baseStart_1548445 : Nat := 118140960795 + 1548445 * 2 ^ 59
def prefixEnd_1548445 : Nat := 4983230072969 + 3 ^ 40 * 1548445 * 2
def baseEnd_1548445 : Nat := 265032184017099811838779

theorem tailTrace_1548445 : CollatzResearch.WordTrace tailWord_1548445 prefixEnd_1548445 265032184017099811838779 := by
  unfold tailWord_1548445
  simp only [CollatzResearch.WordTrace]
  refine ⟨56476428875255693196902789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37650952583503795464601859 56476428875255693196902789)
  ·
    refine ⟨10589330414110442474419273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56476428875255693196902789 10589330414110442474419273)
    ·
      refine ⟨7941997810582831855814455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10589330414110442474419273 7941997810582831855814455)
      ·
        refine ⟨11912996715874247783721683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7941997810582831855814455 11912996715874247783721683)
        ·
          refine ⟨17869495073811371675582525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11912996715874247783721683 17869495073811371675582525)
          ·
            refine ⟨6701060652679264378343447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17869495073811371675582525 6701060652679264378343447)
            ·
              refine ⟨10051590979018896567515171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6701060652679264378343447 10051590979018896567515171)
              ·
                refine ⟨15077386468528344851272757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10051590979018896567515171 15077386468528344851272757)
                ·
                  refine ⟨1413504981424532329806821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15077386468528344851272757 1413504981424532329806821)
                  ·
                    refine ⟨265032184017099811838779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1413504981424532329806821 265032184017099811838779)
                    ·
                      rfl

theorem cell23_1548445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_1548445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1548445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1548445 prefixEnd_1548445 := by exact prefixLift 1548445
  have htrace : WordTrace (prefixWord ++ tailWord_1548445) baseStart_1548445 baseEnd_1548445 := by
    simpa [prefixWord, tailWord_1548445, baseEnd_1548445] using wordTrace_append hprefix tailTrace_1548445
  have hstable : (prefixWord ++ tailWord_1548445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548445).length < 2 ^ (prefixWord ++ tailWord_1548445).sum := by decide
  have hdescent : baseEnd_1548445 < baseStart_1548445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548495 : List Nat := [1, 1, 2, 1, 1, 3, 3, 1, 3, 5, 2]
def baseStart_1548495 : Nat := 118140960795 + 1548495 * 2 ^ 59
def prefixEnd_1548495 : Nat := 4983230072969 + 3 ^ 40 * 1548495 * 2
def baseEnd_1548495 : Nat := 795122226084024239891107

theorem tailTrace_1548495 : CollatzResearch.WordTrace tailWord_1548495 prefixEnd_1548495 795122226084024239891107 := by
  unfold tailWord_1548495
  simp only [CollatzResearch.WordTrace]
  refine ⟨56478252525074551736222939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37652168350049701157481959 56478252525074551736222939)
  ·
    refine ⟨84717378787611827604334409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56478252525074551736222939 84717378787611827604334409)
    ·
      refine ⟨63538034090708870703250807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84717378787611827604334409 63538034090708870703250807)
      ·
        refine ⟨95307051136063306054876211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63538034090708870703250807 95307051136063306054876211)
        ·
          refine ⟨142960576704094959082314317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95307051136063306054876211 142960576704094959082314317)
          ·
            refine ⟨53610216264035609655867869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142960576704094959082314317 53610216264035609655867869)
            ·
              refine ⟨20103831099013353620950451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53610216264035609655867869 20103831099013353620950451)
              ·
                refine ⟨30155746648520030431425677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20103831099013353620950451 30155746648520030431425677)
                ·
                  refine ⟨11308404993195011411784629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30155746648520030431425677 11308404993195011411784629)
                  ·
                    refine ⟨1060162968112032319854809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11308404993195011411784629 1060162968112032319854809)
                    ·
                      refine ⟨795122226084024239891107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1060162968112032319854809 795122226084024239891107)
                      ·
                        rfl

theorem cell23_1548495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 5, 2].length) (baseStart_1548495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1548495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1548495 prefixEnd_1548495 := by exact prefixLift 1548495
  have htrace : WordTrace (prefixWord ++ tailWord_1548495) baseStart_1548495 baseEnd_1548495 := by
    simpa [prefixWord, tailWord_1548495, baseEnd_1548495] using wordTrace_append hprefix tailTrace_1548495
  have hstable : (prefixWord ++ tailWord_1548495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548495).length < 2 ^ (prefixWord ++ tailWord_1548495).sum := by decide
  have hdescent : baseEnd_1548495 < baseStart_1548495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548505 : List Nat := [1, 2, 1, 2, 3, 1, 3, 4, 1, 5]
def baseStart_1548505 : Nat := 118140960795 + 1548505 * 2 ^ 59
def prefixEnd_1548505 : Nat := 4983230072969 + 3 ^ 40 * 1548505 * 2
def baseEnd_1548505 : Nat := 265042453630189733588687

theorem tailTrace_1548505 : CollatzResearch.WordTrace tailWord_1548505 prefixEnd_1548505 265042453630189733588687 := by
  unfold tailWord_1548505
  simp only [CollatzResearch.WordTrace]
  refine ⟨56478617255038323444086969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37652411503358882296057979 56478617255038323444086969)
  ·
    refine ⟨42358962941278742583065227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56478617255038323444086969 42358962941278742583065227)
    ·
      refine ⟨63538444411918113874597841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42358962941278742583065227 63538444411918113874597841)
      ·
        refine ⟨47653833308938585405948381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63538444411918113874597841 47653833308938585405948381)
        ·
          refine ⟨17870187490851969527230643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47653833308938585405948381 17870187490851969527230643)
          ·
            refine ⟨26805281236277954290845965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17870187490851969527230643 26805281236277954290845965)
            ·
              refine ⟨10051980463604232859067237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26805281236277954290845965 10051980463604232859067237)
              ·
                refine ⟨1884746336925793661075107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10051980463604232859067237 1884746336925793661075107)
                ·
                  refine ⟨2827119505388690491612661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1884746336925793661075107 2827119505388690491612661)
                  ·
                    refine ⟨265042453630189733588687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2827119505388690491612661 265042453630189733588687)
                    ·
                      rfl

theorem cell23_1548505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 4, 1, 5].length) (baseStart_1548505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1548505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1548505 prefixEnd_1548505 := by exact prefixLift 1548505
  have htrace : WordTrace (prefixWord ++ tailWord_1548505) baseStart_1548505 baseEnd_1548505 := by
    simpa [prefixWord, tailWord_1548505, baseEnd_1548505] using wordTrace_append hprefix tailTrace_1548505
  have hstable : (prefixWord ++ tailWord_1548505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548505).length < 2 ^ (prefixWord ++ tailWord_1548505).sum := by decide
  have hdescent : baseEnd_1548505 < baseStart_1548505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548512 : List Nat := [2, 1, 1, 3, 1, 3, 2, 3, 2, 3, 2]
def baseStart_1548512 : Nat := 118140960795 + 1548512 * 2 ^ 59
def prefixEnd_1548512 : Nat := 4983230072969 + 3 ^ 40 * 1548512 * 2
def baseEnd_1548512 : Nat := 795130955255150673378529

theorem tailTrace_1548512 : CollatzResearch.WordTrace tailWord_1548512 prefixEnd_1548512 795130955255150673378529 := by
  unfold tailWord_1548512
  simp only [CollatzResearch.WordTrace]
  refine ⟨28239436283006481819795895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37652581710675309093061193 28239436283006481819795895)
  ·
    refine ⟨42359154424509722729693843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28239436283006481819795895 42359154424509722729693843)
    ·
      refine ⟨63538731636764584094540765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42359154424509722729693843 63538731636764584094540765)
      ·
        refine ⟨23827024363786719035452787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63538731636764584094540765 23827024363786719035452787)
        ·
          refine ⟨35740536545680078553179181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23827024363786719035452787 35740536545680078553179181)
          ·
            refine ⟨13402701204630029457442193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35740536545680078553179181 13402701204630029457442193)
            ·
              refine ⟨10052025903472522093081645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13402701204630029457442193 10052025903472522093081645)
              ·
                refine ⟨3769509713802195784905617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10052025903472522093081645 3769509713802195784905617)
                ·
                  refine ⟨2827132285351646838679213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3769509713802195784905617 2827132285351646838679213)
                  ·
                    refine ⟨1060174607006867564504705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2827132285351646838679213 1060174607006867564504705)
                    ·
                      refine ⟨795130955255150673378529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1060174607006867564504705 795130955255150673378529)
                      ·
                        rfl

theorem cell23_1548512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3, 2, 3, 2].length) (baseStart_1548512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1548512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1548512 prefixEnd_1548512 := by exact prefixLift 1548512
  have htrace : WordTrace (prefixWord ++ tailWord_1548512) baseStart_1548512 baseEnd_1548512 := by
    simpa [prefixWord, tailWord_1548512, baseEnd_1548512] using wordTrace_append hprefix tailTrace_1548512
  have hstable : (prefixWord ++ tailWord_1548512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548512).length < 2 ^ (prefixWord ++ tailWord_1548512).sum := by decide
  have hdescent : baseEnd_1548512 < baseStart_1548512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548542 : List Nat := [4, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4]
def baseStart_1548542 : Nat := 118140960795 + 1548542 * 2 ^ 59
def prefixEnd_1548542 : Nat := 4983230072969 + 3 ^ 40 * 1548542 * 2
def baseEnd_1548542 : Nat := 795146359674785556003391

theorem tailTrace_1548542 : CollatzResearch.WordTrace tailWord_1548542 prefixEnd_1548542 795146359674785556003391 := by
  unfold tailWord_1548542
  simp only [CollatzResearch.WordTrace]
  refine ⟨7059995844488034845397985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37653311170602852508789253 7059995844488034845397985)
  ·
    refine ⟨5294996883366026134048489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7059995844488034845397985 5294996883366026134048489)
    ·
      refine ⟨3971247662524519600536367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5294996883366026134048489 3971247662524519600536367)
      ·
        refine ⟨5956871493786779400804551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3971247662524519600536367 5956871493786779400804551)
        ·
          refine ⟨8935307240680169101206827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5956871493786779400804551 8935307240680169101206827)
          ·
            refine ⟨13402960861020253651810241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8935307240680169101206827 13402960861020253651810241)
            ·
              refine ⟨10052220645765190238857681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13402960861020253651810241 10052220645765190238857681)
              ·
                refine ⟨7539165484323892679143261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10052220645765190238857681 7539165484323892679143261)
                ·
                  refine ⟨2827187056621459754678723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7539165484323892679143261 2827187056621459754678723)
                  ·
                    refine ⟨4240780584932189632018085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2827187056621459754678723 4240780584932189632018085)
                    ·
                      refine ⟨795146359674785556003391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4240780584932189632018085 795146359674785556003391)
                      ·
                        rfl

theorem cell23_1548542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_1548542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1548542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1548542 prefixEnd_1548542 := by exact prefixLift 1548542
  have htrace : WordTrace (prefixWord ++ tailWord_1548542) baseStart_1548542 baseEnd_1548542 := by
    simpa [prefixWord, tailWord_1548542, baseEnd_1548542] using wordTrace_append hprefix tailTrace_1548542
  have hstable : (prefixWord ++ tailWord_1548542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548542).length < 2 ^ (prefixWord ++ tailWord_1548542).sum := by decide
  have hdescent : baseEnd_1548542 < baseStart_1548542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548545 : List Nat := [1, 2, 4, 1, 1, 2, 1, 4, 1, 1, 5]
def baseStart_1548545 : Nat := 118140960795 + 1548545 * 2 ^ 59
def prefixEnd_1548545 : Nat := 4983230072969 + 3 ^ 40 * 1548545 * 2
def baseEnd_1548545 : Nat := 795147900116749044265877

theorem tailTrace_1548545 : CollatzResearch.WordTrace tailWord_1548545 prefixEnd_1548545 795147900116749044265877 := by
  unfold tailWord_1548545
  simp only [CollatzResearch.WordTrace]
  refine ⟨56480076174893410275543089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37653384116595606850362059 56480076174893410275543089)
  ·
    refine ⟨42360057131170057706657317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56480076174893410275543089 42360057131170057706657317)
    ·
      refine ⟨7942510712094385819998247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42360057131170057706657317 7942510712094385819998247)
      ·
        refine ⟨11913766068141578729997371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7942510712094385819998247 11913766068141578729997371)
        ·
          refine ⟨17870649102212368094996057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11913766068141578729997371 17870649102212368094996057)
          ·
            refine ⟨13402986826659276071247043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17870649102212368094996057 13402986826659276071247043)
            ·
              refine ⟨20104480239988914106870565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13402986826659276071247043 20104480239988914106870565)
              ·
                refine ⟨3769590044997921395038231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20104480239988914106870565 3769590044997921395038231)
                ·
                  refine ⟨5654385067496882092557347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3769590044997921395038231 5654385067496882092557347)
                  ·
                    refine ⟨8481577601245323138836021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5654385067496882092557347 8481577601245323138836021)
                    ·
                      refine ⟨795147900116749044265877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8481577601245323138836021 795147900116749044265877)
                      ·
                        rfl

theorem cell23_1548545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_1548545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1548545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1548545 prefixEnd_1548545 := by exact prefixLift 1548545
  have htrace : WordTrace (prefixWord ++ tailWord_1548545) baseStart_1548545 baseEnd_1548545 := by
    simpa [prefixWord, tailWord_1548545, baseEnd_1548545] using wordTrace_append hprefix tailTrace_1548545
  have hstable : (prefixWord ++ tailWord_1548545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548545).length < 2 ^ (prefixWord ++ tailWord_1548545).sum := by decide
  have hdescent : baseEnd_1548545 < baseStart_1548545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548555 : List Nat := [1, 1, 1, 1, 5, 2, 2, 3, 1, 2, 4]
def baseStart_1548555 : Nat := 118140960795 + 1548555 * 2 ^ 59
def prefixEnd_1548555 : Nat := 4983230072969 + 3 ^ 40 * 1548555 * 2
def baseEnd_1548555 : Nat := 795153034923294005140831

theorem tailTrace_1548555 : CollatzResearch.WordTrace tailWord_1548555 prefixEnd_1548555 795153034923294005140831 := by
  unfold tailWord_1548555
  simp only [CollatzResearch.WordTrace]
  refine ⟨56480440904857181983407119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37653627269904787988938079 56480440904857181983407119)
  ·
    refine ⟨84720661357285772975110679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56480440904857181983407119 84720661357285772975110679)
    ·
      refine ⟨127080992035928659462666019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84720661357285772975110679 127080992035928659462666019)
      ·
        refine ⟨190621488053892989193999029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127080992035928659462666019 190621488053892989193999029)
        ·
          refine ⟨17870764505052467736937409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 190621488053892989193999029 17870764505052467736937409)
          ·
            refine ⟨13403073378789350802703057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17870764505052467736937409 13403073378789350802703057)
            ·
              refine ⟨10052305034092013102027293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13403073378789350802703057 10052305034092013102027293)
              ·
                refine ⟨3769614387784504913260235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10052305034092013102027293 3769614387784504913260235)
                ·
                  refine ⟨5654421581676757369890353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3769614387784504913260235 5654421581676757369890353)
                  ·
                    refine ⟨4240816186257568027417765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5654421581676757369890353 4240816186257568027417765)
                    ·
                      refine ⟨795153034923294005140831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4240816186257568027417765 795153034923294005140831)
                      ·
                        rfl

theorem cell23_1548555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3, 1, 2, 4].length) (baseStart_1548555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1548555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1548555 prefixEnd_1548555 := by exact prefixLift 1548555
  have htrace : WordTrace (prefixWord ++ tailWord_1548555) baseStart_1548555 baseEnd_1548555 := by
    simpa [prefixWord, tailWord_1548555, baseEnd_1548555] using wordTrace_append hprefix tailTrace_1548555
  have hstable : (prefixWord ++ tailWord_1548555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548555).length < 2 ^ (prefixWord ++ tailWord_1548555).sum := by decide
  have hdescent : baseEnd_1548555 < baseStart_1548555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548579 : List Nat := [1, 1, 1, 4, 2, 2, 5, 1, 1, 2, 3]
def baseStart_1548579 : Nat := 118140960795 + 1548579 * 2 ^ 59
def prefixEnd_1548579 : Nat := 4983230072969 + 3 ^ 40 * 1548579 * 2
def baseEnd_1548579 : Nat := 795165358459001911240721

theorem tailTrace_1548579 : CollatzResearch.WordTrace tailWord_1548579 prefixEnd_1548579 795165358459001911240721 := by
  unfold tailWord_1548579
  simp only [CollatzResearch.WordTrace]
  refine ⟨56481316256770234082280791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37654210837846822721520527 56481316256770234082280791)
  ·
    refine ⟨84721974385155351123421187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56481316256770234082280791 84721974385155351123421187)
    ·
      refine ⟨127082961577733026685131781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84721974385155351123421187 127082961577733026685131781)
      ·
        refine ⟨23828055295824942503462209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127082961577733026685131781 23828055295824942503462209)
        ·
          refine ⟨17871041471868706877596657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23828055295824942503462209 17871041471868706877596657)
          ·
            refine ⟨13403281103901530158197493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17871041471868706877596657 13403281103901530158197493)
            ·
              refine ⟨1256557603490768452331015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13403281103901530158197493 1256557603490768452331015)
              ·
                refine ⟨1884836405236152678496523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1256557603490768452331015 1884836405236152678496523)
                ·
                  refine ⟨2827254607854229017744785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1884836405236152678496523 2827254607854229017744785)
                  ·
                    refine ⟨2120440955890671763308589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2827254607854229017744785 2120440955890671763308589)
                    ·
                      refine ⟨795165358459001911240721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2120440955890671763308589 795165358459001911240721)
                      ·
                        rfl

theorem cell23_1548579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5, 1, 1, 2, 3].length) (baseStart_1548579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1548579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1548579 prefixEnd_1548579 := by exact prefixLift 1548579
  have htrace : WordTrace (prefixWord ++ tailWord_1548579) baseStart_1548579 baseEnd_1548579 := by
    simpa [prefixWord, tailWord_1548579, baseEnd_1548579] using wordTrace_append hprefix tailTrace_1548579
  have hstable : (prefixWord ++ tailWord_1548579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548579).length < 2 ^ (prefixWord ++ tailWord_1548579).sum := by decide
  have hdescent : baseEnd_1548579 < baseStart_1548579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548586 : List Nat := [3, 1, 4, 2, 2, 1, 2, 2, 2, 4]
def baseStart_1548586 : Nat := 118140960795 + 1548586 * 2 ^ 59
def prefixEnd_1548586 : Nat := 4983230072969 + 3 ^ 40 * 1548586 * 2
def baseEnd_1548586 : Nat := 265056317607861127951063

theorem tailTrace_1548586 : CollatzResearch.WordTrace tailWord_1548586 prefixEnd_1548586 265056317607861127951063 := by
  unfold tailWord_1548586
  simp only [CollatzResearch.WordTrace]
  refine ⟨14120392891936218569446403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37654381045163249518523741 14120392891936218569446403)
  ·
    refine ⟨21180589337904327854169605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14120392891936218569446403 21180589337904327854169605)
    ·
      refine ⟨3971360500857061472656801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21180589337904327854169605 3971360500857061472656801)
      ·
        refine ⟨2978520375642796104492601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3971360500857061472656801 2978520375642796104492601)
        ·
          refine ⟨2233890281732097078369451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2978520375642796104492601 2233890281732097078369451)
          ·
            refine ⟨3350835422598145617554177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2233890281732097078369451 3350835422598145617554177)
            ·
              refine ⟨2513126566948609213165633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3350835422598145617554177 2513126566948609213165633)
              ·
                refine ⟨1884844925211456909874225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2513126566948609213165633 1884844925211456909874225)
                ·
                  refine ⟨1413633693908592682405669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1884844925211456909874225 1413633693908592682405669)
                  ·
                    refine ⟨265056317607861127951063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1413633693908592682405669 265056317607861127951063)
                    ·
                      rfl

theorem cell23_1548586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_1548586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1548586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1548586 prefixEnd_1548586 := by exact prefixLift 1548586
  have htrace : WordTrace (prefixWord ++ tailWord_1548586) baseStart_1548586 baseEnd_1548586 := by
    simpa [prefixWord, tailWord_1548586, baseEnd_1548586] using wordTrace_append hprefix tailTrace_1548586
  have hstable : (prefixWord ++ tailWord_1548586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548586).length < 2 ^ (prefixWord ++ tailWord_1548586).sum := by decide
  have hdescent : baseEnd_1548586 < baseStart_1548586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548593 : List Nat := [1, 2, 2, 3, 4, 1, 1, 4, 1, 2, 2]
def baseStart_1548593 : Nat := 118140960795 + 1548593 * 2 ^ 59
def prefixEnd_1548593 : Nat := 4983230072969 + 3 ^ 40 * 1548593 * 2
def baseEnd_1548593 : Nat := 795172547188164856465657

theorem tailTrace_1548593 : CollatzResearch.WordTrace tailWord_1548593 prefixEnd_1548593 795172547188164856465657 := by
  unfold tailWord_1548593
  simp only [CollatzResearch.WordTrace]
  refine ⟨56481826878719514473290433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37654551252479676315526955 56481826878719514473290433)
  ·
    refine ⟨42361370159039635854967825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56481826878719514473290433 42361370159039635854967825)
    ·
      refine ⟨31771027619279726891225869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42361370159039635854967825 31771027619279726891225869)
      ·
        refine ⟨11914135357229897584209701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31771027619279726891225869 11914135357229897584209701)
        ·
          refine ⟨2233900379480605797039319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11914135357229897584209701 2233900379480605797039319)
          ·
            refine ⟨3350850569220908695558979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2233900379480605797039319 3350850569220908695558979)
            ·
              refine ⟨5026275853831363043338469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3350850569220908695558979 5026275853831363043338469)
              ·
                refine ⟨942426722593380570625963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5026275853831363043338469 942426722593380570625963)
                ·
                  refine ⟨1413640083890070855938945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 942426722593380570625963 1413640083890070855938945)
                  ·
                    refine ⟨1060230062917553141954209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1413640083890070855938945 1060230062917553141954209)
                    ·
                      refine ⟨795172547188164856465657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1060230062917553141954209 795172547188164856465657)
                      ·
                        rfl

theorem cell23_1548593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 4, 1, 2, 2].length) (baseStart_1548593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1548593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1548593 prefixEnd_1548593 := by exact prefixLift 1548593
  have htrace : WordTrace (prefixWord ++ tailWord_1548593) baseStart_1548593 baseEnd_1548593 := by
    simpa [prefixWord, tailWord_1548593, baseEnd_1548593] using wordTrace_append hprefix tailTrace_1548593
  have hstable : (prefixWord ++ tailWord_1548593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548593).length < 2 ^ (prefixWord ++ tailWord_1548593).sum := by decide
  have hdescent : baseEnd_1548593 < baseStart_1548593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548615 : List Nat := [1, 1, 4, 1, 2, 2, 1, 2, 2, 3, 4]
def baseStart_1548615 : Nat := 118140960795 + 1548615 * 2 ^ 59
def prefixEnd_1548615 : Nat := 4983230072969 + 3 ^ 40 * 1548615 * 2
def baseEnd_1548615 : Nat := 795183843762563770390555

theorem tailTrace_1548615 : CollatzResearch.WordTrace tailWord_1548615 prefixEnd_1548615 795183843762563770390555 := by
  unfold tailWord_1548615
  simp only [CollatzResearch.WordTrace]
  refine ⟨56482629284639812230591299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37655086189759874820394199 56482629284639812230591299)
  ·
    refine ⟨84723943926959718345886949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56482629284639812230591299 84723943926959718345886949)
    ·
      refine ⟨15885739486304947189853803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84723943926959718345886949 15885739486304947189853803)
      ·
        refine ⟨23828609229457420784780705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15885739486304947189853803 23828609229457420784780705)
        ·
          refine ⟨17871456922093065588585529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23828609229457420784780705 17871456922093065588585529)
          ·
            refine ⟨13403592691569799191439147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17871456922093065588585529 13403592691569799191439147)
            ·
              refine ⟨20105389037354698787158721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13403592691569799191439147 20105389037354698787158721)
              ·
                refine ⟨15079041778016024090369041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20105389037354698787158721 15079041778016024090369041)
                ·
                  refine ⟨11309281333512018067776781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15079041778016024090369041 11309281333512018067776781)
                  ·
                    refine ⟨4240980500067006775416293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11309281333512018067776781 4240980500067006775416293)
                    ·
                      refine ⟨795183843762563770390555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4240980500067006775416293 795183843762563770390555)
                      ·
                        rfl

theorem cell23_1548615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_1548615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1548615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1548615 prefixEnd_1548615 := by exact prefixLift 1548615
  have htrace : WordTrace (prefixWord ++ tailWord_1548615) baseStart_1548615 baseEnd_1548615 := by
    simpa [prefixWord, tailWord_1548615, baseEnd_1548615] using wordTrace_append hprefix tailTrace_1548615
  have hstable : (prefixWord ++ tailWord_1548615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548615).length < 2 ^ (prefixWord ++ tailWord_1548615).sum := by decide
  have hdescent : baseEnd_1548615 < baseStart_1548615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548632 : List Nat := [2, 1, 2, 2, 1, 1, 2, 3, 3, 4, 2]
def baseStart_1548632 : Nat := 118140960795 + 1548632 * 2 ^ 59
def prefixEnd_1548632 : Nat := 4983230072969 + 3 ^ 40 * 1548632 * 2
def baseEnd_1548632 : Nat := 795192572933690203877977

theorem tailTrace_1548632 : CollatzResearch.WordTrace tailWord_1548632 prefixEnd_1548632 795192572933690203877977 := by
  unfold tailWord_1548632
  simp only [CollatzResearch.WordTrace]
  refine ⟨28241624662789112066980075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37655499550385482755973433 28241624662789112066980075)
  ·
    refine ⟨42362436994183668100470113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28241624662789112066980075 42362436994183668100470113)
    ·
      refine ⟨31771827745637751075352585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42362436994183668100470113 31771827745637751075352585)
      ·
        refine ⟨23828870809228313306514439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31771827745637751075352585 23828870809228313306514439)
        ·
          refine ⟨35743306213842469959771659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23828870809228313306514439 35743306213842469959771659)
          ·
            refine ⟨53614959320763704939657489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35743306213842469959771659 53614959320763704939657489)
            ·
              refine ⟨40211219490572778704743117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53614959320763704939657489 40211219490572778704743117)
              ·
                refine ⟨15079207308964792014278669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40211219490572778704743117 15079207308964792014278669)
                ·
                  refine ⟨5654702740861797005354501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15079207308964792014278669 5654702740861797005354501)
                  ·
                    refine ⟨1060256763911586938503969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5654702740861797005354501 1060256763911586938503969)
                    ·
                      refine ⟨795192572933690203877977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1060256763911586938503969 795192572933690203877977)
                      ·
                        rfl

theorem cell23_1548632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 3, 4, 2].length) (baseStart_1548632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1548632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1548632 prefixEnd_1548632 := by exact prefixLift 1548632
  have htrace : WordTrace (prefixWord ++ tailWord_1548632) baseStart_1548632 baseEnd_1548632 := by
    simpa [prefixWord, tailWord_1548632, baseEnd_1548632] using wordTrace_append hprefix tailTrace_1548632
  have hstable : (prefixWord ++ tailWord_1548632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548632).length < 2 ^ (prefixWord ++ tailWord_1548632).sum := by decide
  have hdescent : baseEnd_1548632 < baseStart_1548632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548642 : List Nat := [3, 3, 2, 1, 1, 2, 1, 2, 2, 6]
def baseStart_1548642 : Nat := 118140960795 + 1548642 * 2 ^ 59
def prefixEnd_1548642 : Nat := 4983230072969 + 3 ^ 40 * 1548642 * 2
def baseEnd_1548642 : Nat := 265065902580078388250977

theorem tailTrace_1548642 : CollatzResearch.WordTrace tailWord_1548642 prefixEnd_1548642 265065902580078388250977 := by
  unfold tailWord_1548642
  simp only [CollatzResearch.WordTrace]
  refine ⟨14120903513885498960456045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37655742703694663894549453 14120903513885498960456045)
  ·
    refine ⟨5295338817707062110171017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14120903513885498960456045 5295338817707062110171017)
    ·
      refine ⟨3971504113280296582628263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5295338817707062110171017 3971504113280296582628263)
      ·
        refine ⟨5957256169920444873942395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3971504113280296582628263 5957256169920444873942395)
        ·
          refine ⟨8935884254880667310913593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5957256169920444873942395 8935884254880667310913593)
          ·
            refine ⟨6701913191160500483185195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8935884254880667310913593 6701913191160500483185195)
            ·
              refine ⟨10052869786740750724777793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6701913191160500483185195 10052869786740750724777793)
              ·
                refine ⟨7539652340055563043583345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10052869786740750724777793 7539652340055563043583345)
                ·
                  refine ⟨5654739255041672282687509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7539652340055563043583345 5654739255041672282687509)
                  ·
                    refine ⟨265065902580078388250977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5654739255041672282687509 265065902580078388250977)
                    ·
                      rfl

theorem cell23_1548642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_1548642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1548642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1548642 prefixEnd_1548642 := by exact prefixLift 1548642
  have htrace : WordTrace (prefixWord ++ tailWord_1548642) baseStart_1548642 baseEnd_1548642 := by
    simpa [prefixWord, tailWord_1548642, baseEnd_1548642] using wordTrace_append hprefix tailTrace_1548642
  have hstable : (prefixWord ++ tailWord_1548642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548642).length < 2 ^ (prefixWord ++ tailWord_1548642).sum := by decide
  have hdescent : baseEnd_1548642 < baseStart_1548642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548649 : List Nat := [1, 2, 1, 1, 1, 3, 5, 1, 4, 2, 2]
def baseStart_1548649 : Nat := 118140960795 + 1548649 * 2 ^ 59
def prefixEnd_1548649 : Nat := 4983230072969 + 3 ^ 40 * 1548649 * 2
def baseEnd_1548649 : Nat := 795201302104816637365399

theorem tailTrace_1548649 : CollatzResearch.WordTrace tailWord_1548649 prefixEnd_1548649 795201302104816637365399 := by
  unfold tailWord_1548649
  simp only [CollatzResearch.WordTrace]
  refine ⟨56483869366516636037329001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37655912911011090691552667 56483869366516636037329001)
  ·
    refine ⟨42362902024887477027996751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56483869366516636037329001 42362902024887477027996751)
    ·
      refine ⟨63544353037331215541995127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42362902024887477027996751 63544353037331215541995127)
      ·
        refine ⟨95316529555996823312992691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63544353037331215541995127 95316529555996823312992691)
        ·
          refine ⟨142974794333995234969489037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95316529555996823312992691 142974794333995234969489037)
          ·
            refine ⟨53615547875248213113558389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142974794333995234969489037 53615547875248213113558389)
            ·
              refine ⟨5026457613304519979396099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53615547875248213113558389 5026457613304519979396099)
              ·
                refine ⟨7539686419956779969094149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5026457613304519979396099 7539686419956779969094149)
                ·
                  refine ⟨1413691203741896244205153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7539686419956779969094149 1413691203741896244205153)
                  ·
                    refine ⟨1060268402806422183153865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1413691203741896244205153 1060268402806422183153865)
                    ·
                      refine ⟨795201302104816637365399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1060268402806422183153865 795201302104816637365399)
                      ·
                        rfl

theorem cell23_1548649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 4, 2, 2].length) (baseStart_1548649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1548649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1548649 prefixEnd_1548649 := by exact prefixLift 1548649
  have htrace : WordTrace (prefixWord ++ tailWord_1548649) baseStart_1548649 baseEnd_1548649 := by
    simpa [prefixWord, tailWord_1548649, baseEnd_1548649] using wordTrace_append hprefix tailTrace_1548649
  have hstable : (prefixWord ++ tailWord_1548649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548649).length < 2 ^ (prefixWord ++ tailWord_1548649).sum := by decide
  have hdescent : baseEnd_1548649 < baseStart_1548649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548706 : List Nat := [3, 3, 1, 2, 1, 1, 5, 2, 5]
def baseStart_1548706 : Nat := 118140960795 + 1548706 * 2 ^ 59
def prefixEnd_1548706 : Nat := 4983230072969 + 3 ^ 40 * 1548706 * 2
def baseEnd_1548706 : Nat := 88358952278013657150293

theorem tailTrace_1548706 : CollatzResearch.WordTrace tailWord_1548706 prefixEnd_1548706 88358952278013657150293 := by
  unfold tailWord_1548706
  simp only [CollatzResearch.WordTrace]
  refine ⟨14121487081827533693038493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37657298884873423181435981 14121487081827533693038493)
  ·
    refine ⟨5295557655685325134889435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14121487081827533693038493 5295557655685325134889435)
    ·
      refine ⟨7943336483527987702334153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5295557655685325134889435 7943336483527987702334153)
      ·
        refine ⟨5957502362645990776750615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7943336483527987702334153 5957502362645990776750615)
        ·
          refine ⟨8936253543968986165125923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5957502362645990776750615 8936253543968986165125923)
          ·
            refine ⟨13404380315953479247688885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8936253543968986165125923 13404380315953479247688885)
            ·
              refine ⟨1256660654620638679470833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13404380315953479247688885 1256660654620638679470833)
              ·
                refine ⟨942495490965479009603125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1256660654620638679470833 942495490965479009603125)
                ·
                  refine ⟨88358952278013657150293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 942495490965479009603125 88358952278013657150293)
                  ·
                    rfl

theorem cell23_1548706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5, 2, 5].length) (baseStart_1548706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1548706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1548706 prefixEnd_1548706 := by exact prefixLift 1548706
  have htrace : WordTrace (prefixWord ++ tailWord_1548706) baseStart_1548706 baseEnd_1548706 := by
    simpa [prefixWord, tailWord_1548706, baseEnd_1548706] using wordTrace_append hprefix tailTrace_1548706
  have hstable : (prefixWord ++ tailWord_1548706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548706).length < 2 ^ (prefixWord ++ tailWord_1548706).sum := by decide
  have hdescent : baseEnd_1548706 < baseStart_1548706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548717 : List Nat := [1, 5, 2, 2, 2, 2, 2, 1, 2, 2, 2]
def baseStart_1548717 : Nat := 118140960795 + 1548717 * 2 ^ 59
def prefixEnd_1548717 : Nat := 4983230072969 + 3 ^ 40 * 1548717 * 2
def baseEnd_1548717 : Nat := 795236218789322371315087

theorem tailTrace_1548717 : CollatzResearch.WordTrace tailWord_1548717 prefixEnd_1548717 795236218789322371315087 := by
  unfold tailWord_1548717
  simp only [CollatzResearch.WordTrace]
  refine ⟨56486349530270283650804405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37657566353513522433869603 56486349530270283650804405)
  ·
    refine ⟨5295595268462839092262913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56486349530270283650804405 5295595268462839092262913)
    ·
      refine ⟨3971696451347129319197185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5295595268462839092262913 3971696451347129319197185)
      ·
        refine ⟨2978772338510346989397889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3971696451347129319197185 2978772338510346989397889)
        ·
          refine ⟨2234079253882760242048417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2978772338510346989397889 2234079253882760242048417)
          ·
            refine ⟨1675559440412070181536313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2234079253882760242048417 1675559440412070181536313)
            ·
              refine ⟨1256669580309052636152235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1675559440412070181536313 1256669580309052636152235)
              ·
                refine ⟨1885004370463578954228353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1256669580309052636152235 1885004370463578954228353)
                ·
                  refine ⟨1413753277847684215671265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1885004370463578954228353 1413753277847684215671265)
                  ·
                    refine ⟨1060314958385763161753449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1413753277847684215671265 1060314958385763161753449)
                    ·
                      refine ⟨795236218789322371315087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1060314958385763161753449 795236218789322371315087)
                      ·
                        rfl

theorem cell23_1548717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_1548717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1548717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1548717 prefixEnd_1548717 := by exact prefixLift 1548717
  have htrace : WordTrace (prefixWord ++ tailWord_1548717) baseStart_1548717 baseEnd_1548717 := by
    simpa [prefixWord, tailWord_1548717, baseEnd_1548717] using wordTrace_append hprefix tailTrace_1548717
  have hstable : (prefixWord ++ tailWord_1548717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548717).length < 2 ^ (prefixWord ++ tailWord_1548717).sum := by decide
  have hdescent : baseEnd_1548717 < baseStart_1548717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548722 : List Nat := [3, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4]
def baseStart_1548722 : Nat := 118140960795 + 1548722 * 2 ^ 59
def prefixEnd_1548722 : Nat := 4983230072969 + 3 ^ 40 * 1548722 * 2
def baseEnd_1548722 : Nat := 795238786192594851752563

theorem tailTrace_1548722 : CollatzResearch.WordTrace tailWord_1548722 prefixEnd_1548722 795238786192594851752563 := by
  unfold tailWord_1548722
  simp only [CollatzResearch.WordTrace]
  refine ⟨14121632973813042376184105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37657687930168113003157613 14121632973813042376184105)
  ·
    refine ⟨10591224730359781782138079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14121632973813042376184105 10591224730359781782138079)
    ·
      refine ⟨15886837095539672673207119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10591224730359781782138079 15886837095539672673207119)
      ·
        refine ⟨23830255643309509009810679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15886837095539672673207119 23830255643309509009810679)
        ·
          refine ⟨35745383464964263514716019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23830255643309509009810679 35745383464964263514716019)
          ·
            refine ⟨53618075197446395272074029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35745383464964263514716019 53618075197446395272074029)
            ·
              refine ⟨20106778199042398227027761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53618075197446395272074029 20106778199042398227027761)
              ·
                refine ⟨15080083649281798670270821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20106778199042398227027761 15080083649281798670270821)
                ·
                  refine ⟨2827515684240337250675779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15080083649281798670270821 2827515684240337250675779)
                  ·
                    refine ⟨4241273526360505876013669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2827515684240337250675779 4241273526360505876013669)
                    ·
                      refine ⟨795238786192594851752563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4241273526360505876013669 795238786192594851752563)
                      ·
                        rfl

theorem cell23_1548722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4].length) (baseStart_1548722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1548722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1548722 prefixEnd_1548722 := by exact prefixLift 1548722
  have htrace : WordTrace (prefixWord ++ tailWord_1548722) baseStart_1548722 baseEnd_1548722 := by
    simpa [prefixWord, tailWord_1548722, baseEnd_1548722] using wordTrace_append hprefix tailTrace_1548722
  have hstable : (prefixWord ++ tailWord_1548722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548722).length < 2 ^ (prefixWord ++ tailWord_1548722).sum := by decide
  have hdescent : baseEnd_1548722 < baseStart_1548722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548735 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 6]
def baseStart_1548735 : Nat := 118140960795 + 1548735 * 2 ^ 59
def prefixEnd_1548735 : Nat := 4983230072969 + 3 ^ 40 * 1548735 * 2
def baseEnd_1548735 : Nat := 795245461441103300890003

theorem tailTrace_1548735 : CollatzResearch.WordTrace tailWord_1548735 prefixEnd_1548735 795245461441103300890003 := by
  unfold tailWord_1548735
  simp only [CollatzResearch.WordTrace]
  refine ⟨56487006044205072724959659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37658004029470048483306439 56487006044205072724959659)
  ·
    refine ⟨84730509066307609087439489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56487006044205072724959659 84730509066307609087439489)
    ·
      refine ⟨63547881799730706815579617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84730509066307609087439489 63547881799730706815579617)
      ·
        refine ⟨47660911349798030111684713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63547881799730706815579617 47660911349798030111684713)
        ·
          refine ⟨35745683512348522583763535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47660911349798030111684713 35745683512348522583763535)
          ·
            refine ⟨53618525268522783875645303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35745683512348522583763535 53618525268522783875645303)
            ·
              refine ⟨80427787902784175813467955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53618525268522783875645303 80427787902784175813467955)
              ·
                refine ⟨120641681854176263720201933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80427787902784175813467955 120641681854176263720201933)
                ·
                  refine ⟨45240630695316098895075725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120641681854176263720201933 45240630695316098895075725)
                  ·
                    refine ⟨16965236510743537085653397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45240630695316098895075725 16965236510743537085653397)
                    ·
                      refine ⟨795245461441103300890003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16965236510743537085653397 795245461441103300890003)
                      ·
                        rfl

theorem cell23_1548735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 6].length) (baseStart_1548735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1548735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1548735 prefixEnd_1548735 := by exact prefixLift 1548735
  have htrace : WordTrace (prefixWord ++ tailWord_1548735) baseStart_1548735 baseEnd_1548735 := by
    simpa [prefixWord, tailWord_1548735, baseEnd_1548735] using wordTrace_append hprefix tailTrace_1548735
  have hstable : (prefixWord ++ tailWord_1548735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548735).length < 2 ^ (prefixWord ++ tailWord_1548735).sum := by decide
  have hdescent : baseEnd_1548735 < baseStart_1548735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548745 : List Nat := [1, 2, 1, 1, 2, 1, 4, 1, 10]
def baseStart_1548745 : Nat := 118140960795 + 1548745 * 2 ^ 59
def prefixEnd_1548745 : Nat := 4983230072969 + 3 ^ 40 * 1548745 * 2
def baseEnd_1548745 : Nat := 88361177360849806862773

theorem tailTrace_1548745 : CollatzResearch.WordTrace tailWord_1548745 prefixEnd_1548745 88361177360849806862773 := by
  unfold tailWord_1548745
  simp only [CollatzResearch.WordTrace]
  refine ⟨56487370774168844432823689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37658247182779229621882459 56487370774168844432823689)
  ·
    refine ⟨42365528080626633324617767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56487370774168844432823689 42365528080626633324617767)
    ·
      refine ⟨63548292120939949986926651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42365528080626633324617767 63548292120939949986926651)
      ·
        refine ⟨95322438181409924980389977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63548292120939949986926651 95322438181409924980389977)
        ·
          refine ⟨71491828636057443735292483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95322438181409924980389977 71491828636057443735292483)
          ·
            refine ⟨107237742954086165602938725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71491828636057443735292483 107237742954086165602938725)
            ·
              refine ⟨20107076803891156050551011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107237742954086165602938725 20107076803891156050551011)
              ·
                refine ⟨30160615205836734075826517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20107076803891156050551011 30160615205836734075826517)
                ·
                  refine ⟨88361177360849806862773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 30160615205836734075826517 88361177360849806862773)
                  ·
                    rfl

theorem cell23_1548745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 10].length) (baseStart_1548745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1548745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1548745 prefixEnd_1548745 := by exact prefixLift 1548745
  have htrace : WordTrace (prefixWord ++ tailWord_1548745) baseStart_1548745 baseEnd_1548745 := by
    simpa [prefixWord, tailWord_1548745, baseEnd_1548745] using wordTrace_append hprefix tailTrace_1548745
  have hstable : (prefixWord ++ tailWord_1548745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548745).length < 2 ^ (prefixWord ++ tailWord_1548745).sum := by decide
  have hdescent : baseEnd_1548745 < baseStart_1548745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548772 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 4, 5, 3]
def baseStart_1548772 : Nat := 118140960795 + 1548772 * 2 ^ 59
def prefixEnd_1548772 : Nat := 4983230072969 + 3 ^ 40 * 1548772 * 2
def baseEnd_1548772 : Nat := 795264460225319656127333

theorem tailTrace_1548772 : CollatzResearch.WordTrace tailWord_1548772 prefixEnd_1548772 795264460225319656127333 := by
  unfold tailWord_1548772
  simp only [CollatzResearch.WordTrace]
  refine ⟨28244177772535514022028285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37658903696714018696037713 28244177772535514022028285)
  ·
    refine ⟨10591566664700817758260607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28244177772535514022028285 10591566664700817758260607)
    ·
      refine ⟨15887349997051226637390911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10591566664700817758260607 15887349997051226637390911)
      ·
        refine ⟨23831024995576839956086367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15887349997051226637390911 23831024995576839956086367)
        ·
          refine ⟨35746537493365259934129551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23831024995576839956086367 35746537493365259934129551)
          ·
            refine ⟨53619806240047889901194327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35746537493365259934129551 53619806240047889901194327)
            ·
              refine ⟨80429709360071834851791491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53619806240047889901194327 80429709360071834851791491)
              ·
                refine ⟨120644564040107752277687237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80429709360071834851791491 120644564040107752277687237)
                ·
                  refine ⟨22620855757520203552066357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120644564040107752277687237 22620855757520203552066357)
                  ·
                    refine ⟨2120705227267519083006221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22620855757520203552066357 2120705227267519083006221)
                    ·
                      refine ⟨795264460225319656127333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2120705227267519083006221 795264460225319656127333)
                      ·
                        rfl

theorem cell23_1548772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 4, 5, 3].length) (baseStart_1548772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1548772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1548772 prefixEnd_1548772 := by exact prefixLift 1548772
  have htrace : WordTrace (prefixWord ++ tailWord_1548772) baseStart_1548772 baseEnd_1548772 := by
    simpa [prefixWord, tailWord_1548772, baseEnd_1548772] using wordTrace_append hprefix tailTrace_1548772
  have hstable : (prefixWord ++ tailWord_1548772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548772).length < 2 ^ (prefixWord ++ tailWord_1548772).sum := by decide
  have hdescent : baseEnd_1548772 < baseStart_1548772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548792 : List Nat := [2, 1, 2, 1, 1, 4, 1, 3, 3, 5]
def baseStart_1548792 : Nat := 118140960795 + 1548792 * 2 ^ 59
def prefixEnd_1548792 : Nat := 4983230072969 + 3 ^ 40 * 1548792 * 2
def baseEnd_1548792 : Nat := 265091576612803192625747

theorem tailTrace_1548792 : CollatzResearch.WordTrace tailWord_1548792 prefixEnd_1548792 265091576612803192625747 := by
  unfold tailWord_1548792
  simp only [CollatzResearch.WordTrace]
  refine ⟨28244542502499285729892315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37659390003332380973189753 28244542502499285729892315)
  ·
    refine ⟨42366813753748928594838473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28244542502499285729892315 42366813753748928594838473)
    ·
      refine ⟨31775110315311696446128855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42366813753748928594838473 31775110315311696446128855)
      ·
        refine ⟨47662665472967544669193283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31775110315311696446128855 47662665472967544669193283)
        ·
          refine ⟨71493998209451317003789925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47662665472967544669193283 71493998209451317003789925)
          ·
            refine ⟨13405124664272121938210611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71493998209451317003789925 13405124664272121938210611)
            ·
              refine ⟨20107686996408182907315917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13405124664272121938210611 20107686996408182907315917)
              ·
                refine ⟨7540382623653068590243469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20107686996408182907315917 7540382623653068590243469)
                ·
                  refine ⟨2827643483869900721341301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7540382623653068590243469 2827643483869900721341301)
                  ·
                    refine ⟨265091576612803192625747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2827643483869900721341301 265091576612803192625747)
                    ·
                      rfl

theorem cell23_1548792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 3, 5].length) (baseStart_1548792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1548792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1548792 prefixEnd_1548792 := by exact prefixLift 1548792
  have htrace : WordTrace (prefixWord ++ tailWord_1548792) baseStart_1548792 baseEnd_1548792 := by
    simpa [prefixWord, tailWord_1548792, baseEnd_1548792] using wordTrace_append hprefix tailTrace_1548792
  have hstable : (prefixWord ++ tailWord_1548792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548792).length < 2 ^ (prefixWord ++ tailWord_1548792).sum := by decide
  have hdescent : baseEnd_1548792 < baseStart_1548792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548799 : List Nat := [1, 1, 2, 2, 1, 2, 5, 1, 1, 5, 2]
def baseStart_1548799 : Nat := 118140960795 + 1548799 * 2 ^ 59
def prefixEnd_1548799 : Nat := 4983230072969 + 3 ^ 40 * 1548799 * 2
def baseEnd_1548799 : Nat := 795278324202991050489709

theorem tailTrace_1548799 : CollatzResearch.WordTrace tailWord_1548799 prefixEnd_1548799 795278324202991050489709 := by
  unfold tailWord_1548799
  simp only [CollatzResearch.WordTrace]
  refine ⟨56489340315973211655289451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37659560210648807770192967 56489340315973211655289451)
  ·
    refine ⟨84734010473959817482934177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56489340315973211655289451 84734010473959817482934177)
    ·
      refine ⟨63550507855469863112200633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84734010473959817482934177 63550507855469863112200633)
      ·
        refine ⟨47662880891602397334150475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63550507855469863112200633 47662880891602397334150475)
        ·
          refine ⟨71494321337403596001225713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47662880891602397334150475 71494321337403596001225713)
          ·
            refine ⟨53620741003052697000919285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71494321337403596001225713 53620741003052697000919285)
            ·
              refine ⟨5026944469036190343836183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53620741003052697000919285 5026944469036190343836183)
              ·
                refine ⟨7540416703554285515754275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5026944469036190343836183 7540416703554285515754275)
                ·
                  refine ⟨11310625055331428273631413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7540416703554285515754275 11310625055331428273631413)
                  ·
                    refine ⟨1060371098937321400652945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11310625055331428273631413 1060371098937321400652945)
                    ·
                      refine ⟨795278324202991050489709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1060371098937321400652945 795278324202991050489709)
                      ·
                        rfl

theorem cell23_1548799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 5, 2].length) (baseStart_1548799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1548799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1548799 prefixEnd_1548799 := by exact prefixLift 1548799
  have htrace : WordTrace (prefixWord ++ tailWord_1548799) baseStart_1548799 baseEnd_1548799 := by
    simpa [prefixWord, tailWord_1548799, baseEnd_1548799] using wordTrace_append hprefix tailTrace_1548799
  have hstable : (prefixWord ++ tailWord_1548799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548799).length < 2 ^ (prefixWord ++ tailWord_1548799).sum := by decide
  have hdescent : baseEnd_1548799 < baseStart_1548799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548813 : List Nat := [1, 7, 1, 1, 1, 1, 3, 2, 6]
def baseStart_1548813 : Nat := 118140960795 + 1548813 * 2 ^ 59
def prefixEnd_1548813 : Nat := 4983230072969 + 3 ^ 40 * 1548813 * 2
def baseEnd_1548813 : Nat := 88365056992461555079405

theorem tailTrace_1548813 : CollatzResearch.WordTrace tailWord_1548813 prefixEnd_1548813 88365056992461555079405 := by
  unfold tailWord_1548813
  simp only [CollatzResearch.WordTrace]
  refine ⟨56489850937922492046299093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37659900625281661364199395 56489850937922492046299093)
  ·
    refine ⟨1323980881357558407335135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 56489850937922492046299093 1323980881357558407335135)
    ·
      refine ⟨1985971322036337611002703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1323980881357558407335135 1985971322036337611002703)
      ·
        refine ⟨2978956983054506416504055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1985971322036337611002703 2978956983054506416504055)
        ·
          refine ⟨4468435474581759624756083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2978956983054506416504055 4468435474581759624756083)
          ·
            refine ⟨6702653211872639437134125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4468435474581759624756083 6702653211872639437134125)
            ·
              refine ⟨2513494954452239788925297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6702653211872639437134125 2513494954452239788925297)
              ·
                refine ⟨1885121215839179841693973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2513494954452239788925297 1885121215839179841693973)
                ·
                  refine ⟨88365056992461555079405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1885121215839179841693973 88365056992461555079405)
                  ·
                    rfl

theorem cell23_1548813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_1548813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1548813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1548813 prefixEnd_1548813 := by exact prefixLift 1548813
  have htrace : WordTrace (prefixWord ++ tailWord_1548813) baseStart_1548813 baseEnd_1548813 := by
    simpa [prefixWord, tailWord_1548813, baseEnd_1548813] using wordTrace_append hprefix tailTrace_1548813
  have hstable : (prefixWord ++ tailWord_1548813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548813).length < 2 ^ (prefixWord ++ tailWord_1548813).sum := by decide
  have hdescent : baseEnd_1548813 < baseStart_1548813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548849 : List Nat := [1, 2, 2, 3, 1, 1, 2, 3, 3, 2, 3]
def baseStart_1548849 : Nat := 118140960795 + 1548849 * 2 ^ 59
def prefixEnd_1548849 : Nat := 4983230072969 + 3 ^ 40 * 1548849 * 2
def baseEnd_1548849 : Nat := 795303998235715854864479

theorem tailTrace_1548849 : CollatzResearch.WordTrace tailWord_1548849 prefixEnd_1548849 795303998235715854864479 := by
  unfold tailWord_1548849
  simp only [CollatzResearch.WordTrace]
  refine ⟨56491163965792070194609601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37660775977194713463073067 56491163965792070194609601)
  ·
    refine ⟨42368372974344052645957201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56491163965792070194609601 42368372974344052645957201)
    ·
      refine ⟨31776279730758039484467901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42368372974344052645957201 31776279730758039484467901)
      ·
        refine ⟨11916104899034264806675463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31776279730758039484467901 11916104899034264806675463)
        ·
          refine ⟨17874157348551397210013195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11916104899034264806675463 17874157348551397210013195)
          ·
            refine ⟨26811236022827095815019793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17874157348551397210013195 26811236022827095815019793)
            ·
              refine ⟨20108427017120321861264845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26811236022827095815019793 20108427017120321861264845)
              ·
                refine ⟨7540660131420120697974317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20108427017120321861264845 7540660131420120697974317)
                ·
                  refine ⟨2827747549282545261740369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7540660131420120697974317 2827747549282545261740369)
                  ·
                    refine ⟨2120810661961908946305277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2827747549282545261740369 2120810661961908946305277)
                    ·
                      refine ⟨795303998235715854864479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2120810661961908946305277 795303998235715854864479)
                      ·
                        rfl

theorem cell23_1548849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_1548849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1548849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1548849 prefixEnd_1548849 := by exact prefixLift 1548849
  have htrace : WordTrace (prefixWord ++ tailWord_1548849) baseStart_1548849 baseEnd_1548849 := by
    simpa [prefixWord, tailWord_1548849, baseEnd_1548849] using wordTrace_append hprefix tailTrace_1548849
  have hstable : (prefixWord ++ tailWord_1548849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548849).length < 2 ^ (prefixWord ++ tailWord_1548849).sum := by decide
  have hdescent : baseEnd_1548849 < baseStart_1548849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548889 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 1, 9, 2]
def baseStart_1548889 : Nat := 118140960795 + 1548889 * 2 ^ 59
def prefixEnd_1548889 : Nat := 4983230072969 + 3 ^ 40 * 1548889 * 2
def baseEnd_1548889 : Nat := 795324537461895698364295

theorem tailTrace_1548889 : CollatzResearch.WordTrace tailWord_1548889 prefixEnd_1548889 795324537461895698364295 := by
  unfold tailWord_1548889
  simp only [CollatzResearch.WordTrace]
  refine ⟨56492622885647157026065721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37661748590431438017377147 56492622885647157026065721)
  ·
    refine ⟨42369467164235367769549291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56492622885647157026065721 42369467164235367769549291)
    ·
      refine ⟨63554200746353051654323937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42369467164235367769549291 63554200746353051654323937)
      ·
        refine ⟨47665650559764788740742953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63554200746353051654323937 47665650559764788740742953)
        ·
          refine ⟨35749237919823591555557215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47665650559764788740742953 35749237919823591555557215)
          ·
            refine ⟨53623856879735387333335823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35749237919823591555557215 53623856879735387333335823)
            ·
              refine ⟨80435785319603081000003735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53623856879735387333335823 80435785319603081000003735)
              ·
                refine ⟨120653677979404621500005603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80435785319603081000003735 120653677979404621500005603)
                ·
                  refine ⟨180980516969106932250008405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120653677979404621500005603 180980516969106932250008405)
                  ·
                    refine ⟨1060432716615860931152393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 180980516969106932250008405 1060432716615860931152393)
                    ·
                      refine ⟨795324537461895698364295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1060432716615860931152393 795324537461895698364295)
                      ·
                        rfl

theorem cell23_1548889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 9, 2].length) (baseStart_1548889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1548889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1548889 prefixEnd_1548889 := by exact prefixLift 1548889
  have htrace : WordTrace (prefixWord ++ tailWord_1548889) baseStart_1548889 baseEnd_1548889 := by
    simpa [prefixWord, tailWord_1548889, baseEnd_1548889] using wordTrace_append hprefix tailTrace_1548889
  have hstable : (prefixWord ++ tailWord_1548889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548889).length < 2 ^ (prefixWord ++ tailWord_1548889).sum := by decide
  have hdescent : baseEnd_1548889 < baseStart_1548889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548894 : List Nat := [4, 4, 1, 2, 2, 1, 1, 2, 1, 5]
def baseStart_1548894 : Nat := 118140960795 + 1548894 * 2 ^ 59
def prefixEnd_1548894 : Nat := 4983230072969 + 3 ^ 40 * 1548894 * 2
def baseEnd_1548894 : Nat := 265109034955056059600591

theorem tailTrace_1548894 : CollatzResearch.WordTrace tailWord_1548894 prefixEnd_1548894 265109034955056059600591 := by
  unfold tailWord_1548894
  simp only [CollatzResearch.WordTrace]
  refine ⟨7061600656328630359999717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37661870167086028586665157 7061600656328630359999717)
  ·
    refine ⟨1324050123061618192499947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7061600656328630359999717 1324050123061618192499947)
    ·
      refine ⟨1986075184592427288749921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1324050123061618192499947 1986075184592427288749921)
      ·
        refine ⟨1489556388444320466562441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1986075184592427288749921 1489556388444320466562441)
        ·
          refine ⟨1117167291333240349921831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1489556388444320466562441 1117167291333240349921831)
          ·
            refine ⟨1675750936999860524882747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1117167291333240349921831 1675750936999860524882747)
            ·
              refine ⟨2513626405499790787324121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1675750936999860524882747 2513626405499790787324121)
              ·
                refine ⟨1885219804124843090493091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2513626405499790787324121 1885219804124843090493091)
                ·
                  refine ⟨2827829706187264635739637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1885219804124843090493091 2827829706187264635739637)
                  ·
                    refine ⟨265109034955056059600591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2827829706187264635739637 265109034955056059600591)
                    ·
                      rfl

theorem cell23_1548894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_1548894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1548894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1548894 prefixEnd_1548894 := by exact prefixLift 1548894
  have htrace : WordTrace (prefixWord ++ tailWord_1548894) baseStart_1548894 baseEnd_1548894 := by
    simpa [prefixWord, tailWord_1548894, baseEnd_1548894] using wordTrace_append hprefix tailTrace_1548894
  have hstable : (prefixWord ++ tailWord_1548894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548894).length < 2 ^ (prefixWord ++ tailWord_1548894).sum := by decide
  have hdescent : baseEnd_1548894 < baseStart_1548894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548929 : List Nat := [1, 2, 4, 2, 1, 1, 2, 2, 2, 6]
def baseStart_1548929 : Nat := 118140960795 + 1548929 * 2 ^ 59
def prefixEnd_1548929 : Nat := 4983230072969 + 3 ^ 40 * 1548929 * 2
def baseEnd_1548929 : Nat := 265115025562691847288037

theorem tailTrace_1548929 : CollatzResearch.WordTrace tailWord_1548929 prefixEnd_1548929 265115025562691847288037 := by
  unfold tailWord_1548929
  simp only [CollatzResearch.WordTrace]
  refine ⟨56494081805502243857521841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37662721203668162571681227 56494081805502243857521841)
  ·
    refine ⟨42370561354126682893141381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56494081805502243857521841 42370561354126682893141381)
    ·
      refine ⟨7944480253898753042464009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42370561354126682893141381 7944480253898753042464009)
      ·
        refine ⟨5958360190424064781848007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7944480253898753042464009 5958360190424064781848007)
        ·
          refine ⟨8937540285636097172772011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5958360190424064781848007 8937540285636097172772011)
          ·
            refine ⟨13406310428454145759158017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8937540285636097172772011 13406310428454145759158017)
            ·
              refine ⟨10054732821340609319368513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13406310428454145759158017 10054732821340609319368513)
              ·
                refine ⟨7541049616005456989526385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10054732821340609319368513 7541049616005456989526385)
                ·
                  refine ⟨5655787212004092742144789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7541049616005456989526385 5655787212004092742144789)
                  ·
                    refine ⟨265115025562691847288037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5655787212004092742144789 265115025562691847288037)
                    ·
                      rfl

theorem cell23_1548929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_1548929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1548929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1548929 prefixEnd_1548929 := by exact prefixLift 1548929
  have htrace : WordTrace (prefixWord ++ tailWord_1548929) baseStart_1548929 baseEnd_1548929 := by
    simpa [prefixWord, tailWord_1548929, baseEnd_1548929] using wordTrace_append hprefix tailTrace_1548929
  have hstable : (prefixWord ++ tailWord_1548929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548929).length < 2 ^ (prefixWord ++ tailWord_1548929).sum := by decide
  have hdescent : baseEnd_1548929 < baseStart_1548929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548946 : List Nat := [3, 2, 3, 1, 2, 2, 1, 1, 2, 6]
def baseStart_1548946 : Nat := 118140960795 + 1548946 * 2 ^ 59
def prefixEnd_1548946 : Nat := 4983230072969 + 3 ^ 40 * 1548946 * 2
def baseEnd_1548946 : Nat := 265117935286400658450511

theorem tailTrace_1548946 : CollatzResearch.WordTrace tailWord_1548946 prefixEnd_1548946 265117935286400658450511 := by
  unfold tailWord_1548946
  simp only [CollatzResearch.WordTrace]
  refine ⟨14123675461610163940222673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37663134564293770507260461 14123675461610163940222673)
  ·
    refine ⟨10592756596207622955167005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14123675461610163940222673 10592756596207622955167005)
    ·
      refine ⟨3972283723577858608187627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10592756596207622955167005 3972283723577858608187627)
      ·
        refine ⟨5958425585366787912281441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3972283723577858608187627 5958425585366787912281441)
        ·
          refine ⟨4468819189025090934211081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5958425585366787912281441 4468819189025090934211081)
          ·
            refine ⟨3351614391768818200658311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4468819189025090934211081 3351614391768818200658311)
            ·
              refine ⟨5027421587653227300987467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3351614391768818200658311 5027421587653227300987467)
              ·
                refine ⟨7541132381479840951481201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5027421587653227300987467 7541132381479840951481201)
                ·
                  refine ⟨5655849286109880713610901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7541132381479840951481201 5655849286109880713610901)
                  ·
                    refine ⟨265117935286400658450511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5655849286109880713610901 265117935286400658450511)
                    ·
                      rfl

theorem cell23_1548946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_1548946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1548946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1548946 prefixEnd_1548946 := by exact prefixLift 1548946
  have htrace : WordTrace (prefixWord ++ tailWord_1548946) baseStart_1548946 baseEnd_1548946 := by
    simpa [prefixWord, tailWord_1548946, baseEnd_1548946] using wordTrace_append hprefix tailTrace_1548946
  have hstable : (prefixWord ++ tailWord_1548946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548946).length < 2 ^ (prefixWord ++ tailWord_1548946).sum := by decide
  have hdescent : baseEnd_1548946 < baseStart_1548946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548953 : List Nat := [1, 2, 1, 2, 1, 2, 3, 5, 2, 2, 2]
def baseStart_1548953 : Nat := 118140960795 + 1548953 * 2 ^ 59
def prefixEnd_1548953 : Nat := 4983230072969 + 3 ^ 40 * 1548953 * 2
def baseEnd_1548953 : Nat := 795357400223783447964001

theorem tailTrace_1548953 : CollatzResearch.WordTrace tailWord_1548953 prefixEnd_1548953 795357400223783447964001 := by
  unfold tailWord_1548953
  simp only [CollatzResearch.WordTrace]
  refine ⟨56494957157415295956395513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37663304771610197304263675 56494957157415295956395513)
  ·
    refine ⟨42371217868061471967296635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56494957157415295956395513 42371217868061471967296635)
    ·
      refine ⟨63556826802092207950944953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42371217868061471967296635 63556826802092207950944953)
      ·
        refine ⟨47667620101569155963208715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63556826802092207950944953 47667620101569155963208715)
        ·
          refine ⟨71501430152353733944813073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47667620101569155963208715 71501430152353733944813073)
          ·
            refine ⟨53626072614265300458609805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71501430152353733944813073 53626072614265300458609805)
            ·
              refine ⟨20109777230349487671978677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53626072614265300458609805 20109777230349487671978677)
              ·
                refine ⟨1885291615345264469248001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20109777230349487671978677 1885291615345264469248001)
                ·
                  refine ⟨1413968711508948351936001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1885291615345264469248001 1413968711508948351936001)
                  ·
                    refine ⟨1060476533631711263952001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1413968711508948351936001 1060476533631711263952001)
                    ·
                      refine ⟨795357400223783447964001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1060476533631711263952001 795357400223783447964001)
                      ·
                        rfl

theorem cell23_1548953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 5, 2, 2, 2].length) (baseStart_1548953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1548953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1548953 prefixEnd_1548953 := by exact prefixLift 1548953
  have htrace : WordTrace (prefixWord ++ tailWord_1548953) baseStart_1548953 baseEnd_1548953 := by
    simpa [prefixWord, tailWord_1548953, baseEnd_1548953] using wordTrace_append hprefix tailTrace_1548953
  have hstable : (prefixWord ++ tailWord_1548953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548953).length < 2 ^ (prefixWord ++ tailWord_1548953).sum := by decide
  have hdescent : baseEnd_1548953 < baseStart_1548953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548969 : List Nat := [1, 2, 1, 1, 1, 1, 2, 4, 4, 3, 3]
def baseStart_1548969 : Nat := 118140960795 + 1548969 * 2 ^ 59
def prefixEnd_1548969 : Nat := 4983230072969 + 3 ^ 40 * 1548969 * 2
def baseEnd_1548969 : Nat := 795365615914255385363927

theorem tailTrace_1548969 : CollatzResearch.WordTrace tailWord_1548969 prefixEnd_1548969 795365615914255385363927 := by
  unfold tailWord_1548969
  simp only [CollatzResearch.WordTrace]
  refine ⟨56495540725357330688977961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37663693816904887125985307 56495540725357330688977961)
  ·
    refine ⟨42371655544017998016733471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56495540725357330688977961 42371655544017998016733471)
    ·
      refine ⟨63557483316026997025100207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42371655544017998016733471 63557483316026997025100207)
      ·
        refine ⟨95336224974040495537650311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63557483316026997025100207 95336224974040495537650311)
        ·
          refine ⟨143004337461060743306475467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95336224974040495537650311 143004337461060743306475467)
          ·
            refine ⟨214506506191591114959713201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143004337461060743306475467 214506506191591114959713201)
            ·
              refine ⟨160879879643693336219784901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 214506506191591114959713201 160879879643693336219784901)
              ·
                refine ⟨30164977433192500541209669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 160879879643693336219784901 30164977433192500541209669)
                ·
                  refine ⟨5655933268723593851476813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30164977433192500541209669 5655933268723593851476813)
                  ·
                    refine ⟨2120974975771347694303805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5655933268723593851476813 2120974975771347694303805)
                    ·
                      refine ⟨795365615914255385363927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2120974975771347694303805 795365615914255385363927)
                      ·
                        rfl

theorem cell23_1548969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4, 3, 3].length) (baseStart_1548969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1548969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1548969 prefixEnd_1548969 := by exact prefixLift 1548969
  have htrace : WordTrace (prefixWord ++ tailWord_1548969) baseStart_1548969 baseEnd_1548969 := by
    simpa [prefixWord, tailWord_1548969, baseEnd_1548969] using wordTrace_append hprefix tailTrace_1548969
  have hstable : (prefixWord ++ tailWord_1548969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548969).length < 2 ^ (prefixWord ++ tailWord_1548969).sum := by decide
  have hdescent : baseEnd_1548969 < baseStart_1548969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548974 : List Nat := [4, 1, 4, 1, 1, 3, 2, 1, 1, 3, 2]
def baseStart_1548974 : Nat := 118140960795 + 1548974 * 2 ^ 59
def prefixEnd_1548974 : Nat := 4983230072969 + 3 ^ 40 * 1548974 * 2
def baseEnd_1548974 : Nat := 795368183317527865801405

theorem tailTrace_1548974 : CollatzResearch.WordTrace tailWord_1548974 prefixEnd_1548974 795368183317527865801405 := by
  unfold tailWord_1548974
  simp only [CollatzResearch.WordTrace]
  refine ⟨7061965386292402067863747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37663815393559477695273317 7061965386292402067863747)
  ·
    refine ⟨10592948079438603101795621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7061965386292402067863747 10592948079438603101795621)
    ·
      refine ⟨1986177764894738081586679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10592948079438603101795621 1986177764894738081586679)
      ·
        refine ⟨2979266647342107122380019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1986177764894738081586679 2979266647342107122380019)
        ·
          refine ⟨4468899971013160683570029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2979266647342107122380019 4468899971013160683570029)
          ·
            refine ⟨1675837489129935256338761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4468899971013160683570029 1675837489129935256338761)
            ·
              refine ⟨1256878116847451442254071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1675837489129935256338761 1256878116847451442254071)
              ·
                refine ⟨1885317175271177163381107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1256878116847451442254071 1885317175271177163381107)
                ·
                  refine ⟨2827975762906765745071661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1885317175271177163381107 2827975762906765745071661)
                  ·
                    refine ⟨1060490911090037154401873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2827975762906765745071661 1060490911090037154401873)
                    ·
                      refine ⟨795368183317527865801405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1060490911090037154401873 795368183317527865801405)
                      ·
                        rfl

theorem cell23_1548974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_1548974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1548974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1548974 prefixEnd_1548974 := by exact prefixLift 1548974
  have htrace : WordTrace (prefixWord ++ tailWord_1548974) baseStart_1548974 baseEnd_1548974 := by
    simpa [prefixWord, tailWord_1548974, baseEnd_1548974] using wordTrace_append hprefix tailTrace_1548974
  have hstable : (prefixWord ++ tailWord_1548974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548974).length < 2 ^ (prefixWord ++ tailWord_1548974).sum := by decide
  have hdescent : baseEnd_1548974 < baseStart_1548974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549009 : List Nat := [1, 2, 2, 1, 2, 3, 1, 1, 3, 3, 4]
def baseStart_1549009 : Nat := 118140960795 + 1549009 * 2 ^ 59
def prefixEnd_1549009 : Nat := 4983230072969 + 3 ^ 40 * 1549009 * 2
def baseEnd_1549009 : Nat := 795386155140435228863743

theorem tailTrace_1549009 : CollatzResearch.WordTrace tailWord_1549009 prefixEnd_1549009 795386155140435228863743 := by
  unfold tailWord_1549009
  simp only [CollatzResearch.WordTrace]
  refine ⟨56496999645212417520434081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37664666430141611680289387 56496999645212417520434081)
  ·
    refine ⟨42372749733909313140325561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56496999645212417520434081 42372749733909313140325561)
    ·
      refine ⟨31779562300431984855244171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42372749733909313140325561 31779562300431984855244171)
      ·
        refine ⟨47669343450647977282866257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31779562300431984855244171 47669343450647977282866257)
        ·
          refine ⟨35752007587985982962149693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47669343450647977282866257 35752007587985982962149693)
          ·
            refine ⟨13407002845494743610806135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35752007587985982962149693 13407002845494743610806135)
            ·
              refine ⟨20110504268242115416209203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13407002845494743610806135 20110504268242115416209203)
              ·
                refine ⟨30165756402363173124313805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20110504268242115416209203 30165756402363173124313805)
                ·
                  refine ⟨11312158650886189921617677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30165756402363173124313805 11312158650886189921617677)
                  ·
                    refine ⟨4242059494082321220606629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11312158650886189921617677 4242059494082321220606629)
                    ·
                      refine ⟨795386155140435228863743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4242059494082321220606629 795386155140435228863743)
                      ·
                        rfl

theorem cell23_1549009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 3, 4].length) (baseStart_1549009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1549009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1549009 prefixEnd_1549009 := by exact prefixLift 1549009
  have htrace : WordTrace (prefixWord ++ tailWord_1549009) baseStart_1549009 baseEnd_1549009 := by
    simpa [prefixWord, tailWord_1549009, baseEnd_1549009] using wordTrace_append hprefix tailTrace_1549009
  have hstable : (prefixWord ++ tailWord_1549009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549009).length < 2 ^ (prefixWord ++ tailWord_1549009).sum := by decide
  have hdescent : baseEnd_1549009 < baseStart_1549009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549044 : List Nat := [2, 6, 1, 1, 2, 1, 3, 2, 5]
def baseStart_1549044 : Nat := 118140960795 + 1549044 * 2 ^ 59
def prefixEnd_1549044 : Nat := 4983230072969 + 3 ^ 40 * 1549044 * 2
def baseEnd_1549044 : Nat := 88378236329260287991787

theorem tailTrace_1549044 : CollatzResearch.WordTrace tailWord_1549044 prefixEnd_1549044 88378236329260287991787 := by
  unfold tailWord_1549044
  simp only [CollatzResearch.WordTrace]
  refine ⟨28249138100042809248979093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37665517466723745665305457 28249138100042809248979093)
  ·
    refine ⟨1324178348439506683545895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 28249138100042809248979093 1324178348439506683545895)
    ·
      refine ⟨1986267522659260025318843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1324178348439506683545895 1986267522659260025318843)
      ·
        refine ⟨2979401283988890037978265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1986267522659260025318843 2979401283988890037978265)
        ·
          refine ⟨2234550962991667528483699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2979401283988890037978265 2234550962991667528483699)
          ·
            refine ⟨3351826444487501292725549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2234550962991667528483699 3351826444487501292725549)
            ·
              refine ⟨1256934916682812984772081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3351826444487501292725549 1256934916682812984772081)
              ·
                refine ⟨942701187512109738579061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1256934916682812984772081 942701187512109738579061)
                ·
                  refine ⟨88378236329260287991787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 942701187512109738579061 88378236329260287991787)
                  ·
                    rfl

theorem cell23_1549044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_1549044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1549044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1549044 prefixEnd_1549044 := by exact prefixLift 1549044
  have htrace : WordTrace (prefixWord ++ tailWord_1549044) baseStart_1549044 baseEnd_1549044 := by
    simpa [prefixWord, tailWord_1549044, baseEnd_1549044] using wordTrace_append hprefix tailTrace_1549044
  have hstable : (prefixWord ++ tailWord_1549044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549044).length < 2 ^ (prefixWord ++ tailWord_1549044).sum := by decide
  have hdescent : baseEnd_1549044 < baseStart_1549044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549066 : List Nat := [3, 1, 2, 2, 1, 2, 3, 3, 6]
def baseStart_1549066 : Nat := 118140960795 + 1549066 * 2 ^ 59
def prefixEnd_1549066 : Nat := 4983230072969 + 3 ^ 40 * 1549066 * 2
def baseEnd_1549066 : Nat := 88379491504193500650109

theorem tailTrace_1549066 : CollatzResearch.WordTrace tailWord_1549066 prefixEnd_1549066 88379491504193500650109 := by
  unfold tailWord_1549066
  simp only [CollatzResearch.WordTrace]
  refine ⟨14124769651501479063814763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37666052404003944170172701 14124769651501479063814763)
  ·
    refine ⟨21187154477252218595722145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14124769651501479063814763 21187154477252218595722145)
    ·
      refine ⟨15890365857939163946791609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21187154477252218595722145 15890365857939163946791609)
      ·
        refine ⟨11917774393454372960093707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15890365857939163946791609 11917774393454372960093707)
        ·
          refine ⟨17876661590181559440140561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11917774393454372960093707 17876661590181559440140561)
          ·
            refine ⟨13407496192636169580105421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17876661590181559440140561 13407496192636169580105421)
            ·
              refine ⟨5027811072238563592539533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13407496192636169580105421 5027811072238563592539533)
              ·
                refine ⟨1885429152089461347202325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5027811072238563592539533 1885429152089461347202325)
                ·
                  refine ⟨88379491504193500650109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1885429152089461347202325 88379491504193500650109)
                  ·
                    rfl

theorem cell23_1549066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 3, 6].length) (baseStart_1549066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1549066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1549066 prefixEnd_1549066 := by exact prefixLift 1549066
  have htrace : WordTrace (prefixWord ++ tailWord_1549066) baseStart_1549066 baseEnd_1549066 := by
    simpa [prefixWord, tailWord_1549066, baseEnd_1549066] using wordTrace_append hprefix tailTrace_1549066
  have hstable : (prefixWord ++ tailWord_1549066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549066).length < 2 ^ (prefixWord ++ tailWord_1549066).sum := by decide
  have hdescent : baseEnd_1549066 < baseStart_1549066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549137 : List Nat := [1, 2, 2, 1, 6, 2, 1, 1, 2, 3, 2]
def baseStart_1549137 : Nat := 118140960795 + 1549137 * 2 ^ 59
def prefixEnd_1549137 : Nat := 4983230072969 + 3 ^ 40 * 1549137 * 2
def baseEnd_1549137 : Nat := 795451880664210728063155

theorem tailTrace_1549137 : CollatzResearch.WordTrace tailWord_1549137 prefixEnd_1549137 795451880664210728063155 := by
  unfold tailWord_1549137
  simp only [CollatzResearch.WordTrace]
  refine ⟨56501668188748695381093665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37667778792499130254062443 56501668188748695381093665)
  ·
    refine ⟨42376251141561521535820249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56501668188748695381093665 42376251141561521535820249)
    ·
      refine ⟨31782188356171141151865187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42376251141561521535820249 31782188356171141151865187)
      ·
        refine ⟨47673282534256711727797781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31782188356171141151865187 47673282534256711727797781)
        ·
          refine ⟨2234685118793283362240521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 47673282534256711727797781 2234685118793283362240521)
          ·
            refine ⟨1676013839094962521680391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2234685118793283362240521 1676013839094962521680391)
            ·
              refine ⟨2514020758642443782520587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1676013839094962521680391 2514020758642443782520587)
              ·
                refine ⟨3771031137963665673780881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2514020758642443782520587 3771031137963665673780881)
                ·
                  refine ⟨2828273353472749255335661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3771031137963665673780881 2828273353472749255335661)
                  ·
                    refine ⟨1060602507552280970750873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2828273353472749255335661 1060602507552280970750873)
                    ·
                      refine ⟨795451880664210728063155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1060602507552280970750873 795451880664210728063155)
                      ·
                        rfl

theorem cell23_1549137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 1, 2, 3, 2].length) (baseStart_1549137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1549137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1549137 prefixEnd_1549137 := by exact prefixLift 1549137
  have htrace : WordTrace (prefixWord ++ tailWord_1549137) baseStart_1549137 baseEnd_1549137 := by
    simpa [prefixWord, tailWord_1549137, baseEnd_1549137] using wordTrace_append hprefix tailTrace_1549137
  have hstable : (prefixWord ++ tailWord_1549137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549137).length < 2 ^ (prefixWord ++ tailWord_1549137).sum := by decide
  have hdescent : baseEnd_1549137 < baseStart_1549137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549139 : List Nat := [1, 1, 1, 2, 1, 1, 3, 13]
def baseStart_1549139 : Nat := 118140960795 + 1549139 * 2 ^ 59
def prefixEnd_1549139 : Nat := 4983230072969 + 3 ^ 40 * 1549139 * 2
def baseEnd_1549139 : Nat := 29461218800945174823635

theorem tailTrace_1549139 : CollatzResearch.WordTrace tailWord_1549139 prefixEnd_1549139 29461218800945174823635 := by
  unfold tailWord_1549139
  simp only [CollatzResearch.WordTrace]
  refine ⟨56501741134741449722666471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37667827423160966481777647 56501741134741449722666471)
  ·
    refine ⟨84752611702112174583999707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56501741134741449722666471 84752611702112174583999707)
    ·
      refine ⟨127128917553168261875999561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84752611702112174583999707 127128917553168261875999561)
      ·
        refine ⟨95346688164876196406999671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127128917553168261875999561 95346688164876196406999671)
        ·
          refine ⟨143020032247314294610499507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95346688164876196406999671 143020032247314294610499507)
          ·
            refine ⟨214530048370971441915749261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143020032247314294610499507 214530048370971441915749261)
            ·
              refine ⟨80448768139114290718405973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 214530048370971441915749261 80448768139114290718405973)
              ·
                refine ⟨29461218800945174823635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 80448768139114290718405973 29461218800945174823635)
                ·
                  rfl

theorem cell23_1549139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 13].length) (baseStart_1549139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1549139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1549139 prefixEnd_1549139 := by exact prefixLift 1549139
  have htrace : WordTrace (prefixWord ++ tailWord_1549139) baseStart_1549139 baseEnd_1549139 := by
    simpa [prefixWord, tailWord_1549139, baseEnd_1549139] using wordTrace_append hprefix tailTrace_1549139
  have hstable : (prefixWord ++ tailWord_1549139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549139).length < 2 ^ (prefixWord ++ tailWord_1549139).sum := by decide
  have hdescent : baseEnd_1549139 < baseStart_1549139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549156 : List Nat := [2, 3, 1, 1, 4, 2, 10]
def baseStart_1549156 : Nat := 118140960795 + 1549156 * 2 ^ 59
def prefixEnd_1549156 : Nat := 4983230072969 + 3 ^ 40 * 1549156 * 2
def baseEnd_1549156 : Nat := 9820514034526495725007

theorem tailTrace_1549156 : CollatzResearch.WordTrace tailWord_1549156 prefixEnd_1549156 9820514034526495725007 := by
  unfold tailWord_1549156
  simp only [CollatzResearch.WordTrace]
  refine ⟨28251180587839930813017661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37668240783786574417356881 28251180587839930813017661)
  ·
    refine ⟨10594192720439974054881623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28251180587839930813017661 10594192720439974054881623)
    ·
      refine ⟨15891289080659961082322435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10594192720439974054881623 15891289080659961082322435)
      ·
        refine ⟨23836933620989941623483653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15891289080659961082322435 23836933620989941623483653)
        ·
          refine ⟨4469425053935614054403185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23836933620989941623483653 4469425053935614054403185)
          ·
            refine ⟨3352068790451710540802389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4469425053935614054403185 3352068790451710540802389)
            ·
              refine ⟨9820514034526495725007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3352068790451710540802389 9820514034526495725007)
              ·
                rfl

theorem cell23_1549156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 10].length) (baseStart_1549156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1549156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1549156 prefixEnd_1549156 := by exact prefixLift 1549156
  have htrace : WordTrace (prefixWord ++ tailWord_1549156) baseStart_1549156 baseEnd_1549156 := by
    simpa [prefixWord, tailWord_1549156, baseEnd_1549156] using wordTrace_append hprefix tailTrace_1549156
  have hstable : (prefixWord ++ tailWord_1549156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549156).length < 2 ^ (prefixWord ++ tailWord_1549156).sum := by decide
  have hdescent : baseEnd_1549156 < baseStart_1549156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549160 : List Nat := [2, 1, 4, 2, 1, 2, 3, 2, 2, 4]
def baseStart_1549160 : Nat := 118140960795 + 1549160 * 2 ^ 59
def prefixEnd_1549160 : Nat := 4983230072969 + 3 ^ 40 * 1549160 * 2
def baseEnd_1549160 : Nat := 265154563573088046025183

theorem tailTrace_1549160 : CollatzResearch.WordTrace tailWord_1549160 prefixEnd_1549160 265154563573088046025183 := by
  unfold tailWord_1549160
  simp only [CollatzResearch.WordTrace]
  refine ⟨28251253533832685154590467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37668338045110246872787289 28251253533832685154590467)
  ·
    refine ⟨42376880300749027731885701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28251253533832685154590467 42376880300749027731885701)
    ·
      refine ⟨7945665056390442699728569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42376880300749027731885701 7945665056390442699728569)
      ·
        refine ⟨5959248792292832024796427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7945665056390442699728569 5959248792292832024796427)
        ·
          refine ⟨8938873188439248037194641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5959248792292832024796427 8938873188439248037194641)
          ·
            refine ⟨6704154891329436027895981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8938873188439248037194641 6704154891329436027895981)
            ·
              refine ⟨2514058084248538510460993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6704154891329436027895981 2514058084248538510460993)
              ·
                refine ⟨1885543563186403882845745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2514058084248538510460993 1885543563186403882845745)
                ·
                  refine ⟨1414157672389802912134309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1885543563186403882845745 1414157672389802912134309)
                  ·
                    refine ⟨265154563573088046025183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1414157672389802912134309 265154563573088046025183)
                    ·
                      rfl

theorem cell23_1549160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_1549160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1549160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1549160 prefixEnd_1549160 := by exact prefixLift 1549160
  have htrace : WordTrace (prefixWord ++ tailWord_1549160) baseStart_1549160 baseEnd_1549160 := by
    simpa [prefixWord, tailWord_1549160, baseEnd_1549160] using wordTrace_append hprefix tailTrace_1549160
  have hstable : (prefixWord ++ tailWord_1549160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549160).length < 2 ^ (prefixWord ++ tailWord_1549160).sum := by decide
  have hdescent : baseEnd_1549160 < baseStart_1549160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549183 : List Nat := [1, 1, 2, 2, 1, 1, 7, 1, 1, 3, 3]
def baseStart_1549183 : Nat := 118140960795 + 1549183 * 2 ^ 59
def prefixEnd_1549183 : Nat := 4983230072969 + 3 ^ 40 * 1549183 * 2
def baseEnd_1549183 : Nat := 795475500774317548087943

theorem tailTrace_1549183 : CollatzResearch.WordTrace tailWord_1549183 prefixEnd_1549183 795475500774317548087943 := by
  unfold tailWord_1549183
  simp only [CollatzResearch.WordTrace]
  refine ⟨56503345946582045237268203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37668897297721363491512135 56503345946582045237268203)
  ·
    refine ⟨84755018919873067855902305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56503345946582045237268203 84755018919873067855902305)
    ·
      refine ⟨63566264189904800891926729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84755018919873067855902305 63566264189904800891926729)
      ·
        refine ⟨47674698142428600668945047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63566264189904800891926729 47674698142428600668945047)
        ·
          refine ⟨71512047213642901003417571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47674698142428600668945047 71512047213642901003417571)
          ·
            refine ⟨107268070820464351505126357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71512047213642901003417571 107268070820464351505126357)
            ·
              refine ⟨2514095409854633238401399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 107268070820464351505126357 2514095409854633238401399)
              ·
                refine ⟨3771143114781949857602099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2514095409854633238401399 3771143114781949857602099)
                ·
                  refine ⟨5656714672172924786403149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3771143114781949857602099 5656714672172924786403149)
                  ·
                    refine ⟨2121268002064846794901181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5656714672172924786403149 2121268002064846794901181)
                    ·
                      refine ⟨795475500774317548087943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2121268002064846794901181 795475500774317548087943)
                      ·
                        rfl

theorem cell23_1549183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 1, 1, 3, 3].length) (baseStart_1549183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1549183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1549183 prefixEnd_1549183 := by exact prefixLift 1549183
  have htrace : WordTrace (prefixWord ++ tailWord_1549183) baseStart_1549183 baseEnd_1549183 := by
    simpa [prefixWord, tailWord_1549183, baseEnd_1549183] using wordTrace_append hprefix tailTrace_1549183
  have hstable : (prefixWord ++ tailWord_1549183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549183).length < 2 ^ (prefixWord ++ tailWord_1549183).sum := by decide
  have hdescent : baseEnd_1549183 < baseStart_1549183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549196 : List Nat := [2, 2, 1, 2, 1, 2, 3, 1, 2, 2, 5]
def baseStart_1549196 : Nat := 118140960795 + 1549196 * 2 ^ 59
def prefixEnd_1549196 : Nat := 4983230072969 + 3 ^ 40 * 1549196 * 2
def baseEnd_1549196 : Nat := 795482176022825997225383

theorem tailTrace_1549196 : CollatzResearch.WordTrace tailWord_1549196 prefixEnd_1549196 795482176022825997225383 := by
  unfold tailWord_1549196
  simp only [CollatzResearch.WordTrace]
  refine ⟨28251910047767474228745721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37669213397023298971660961 28251910047767474228745721)
  ·
    refine ⟨21188932535825605671559291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28251910047767474228745721 21188932535825605671559291)
    ·
      refine ⟨31783398803738408507338937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21188932535825605671559291 31783398803738408507338937)
      ·
        refine ⟨23837549102803806380504203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31783398803738408507338937 23837549102803806380504203)
        ·
          refine ⟨35756323654205709570756305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23837549102803806380504203 35756323654205709570756305)
          ·
            refine ⟨26817242740654282178067229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35756323654205709570756305 26817242740654282178067229)
            ·
              refine ⟨10056466027745355816775211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26817242740654282178067229 10056466027745355816775211)
              ·
                refine ⟨15084699041618033725162817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10056466027745355816775211 15084699041618033725162817)
                ·
                  refine ⟨11313524281213525293872113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15084699041618033725162817 11313524281213525293872113)
                  ·
                    refine ⟨8485143210910143970404085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11313524281213525293872113 8485143210910143970404085)
                    ·
                      refine ⟨795482176022825997225383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8485143210910143970404085 795482176022825997225383)
                      ·
                        rfl

theorem cell23_1549196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_1549196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1549196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1549196 prefixEnd_1549196 := by exact prefixLift 1549196
  have htrace : WordTrace (prefixWord ++ tailWord_1549196) baseStart_1549196 baseEnd_1549196 := by
    simpa [prefixWord, tailWord_1549196, baseEnd_1549196] using wordTrace_append hprefix tailTrace_1549196
  have hstable : (prefixWord ++ tailWord_1549196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549196).length < 2 ^ (prefixWord ++ tailWord_1549196).sum := by decide
  have hdescent : baseEnd_1549196 < baseStart_1549196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549216 : List Nat := [2, 1, 1, 4, 1, 1, 2, 1, 4, 6]
def baseStart_1549216 : Nat := 118140960795 + 1549216 * 2 ^ 59
def prefixEnd_1549216 : Nat := 4983230072969 + 3 ^ 40 * 1549216 * 2
def baseEnd_1549216 : Nat := 265164148545305306325097

theorem tailTrace_1549216 : CollatzResearch.WordTrace tailWord_1549216 prefixEnd_1549216 265164148545305306325097 := by
  unfold tailWord_1549216
  simp only [CollatzResearch.WordTrace]
  refine ⟨28252274777731245936609751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37669699703641661248813001 28252274777731245936609751)
  ·
    refine ⟨42378412166596868904914627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28252274777731245936609751 42378412166596868904914627)
    ·
      refine ⟨63567618249895303357371941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42378412166596868904914627 63567618249895303357371941)
      ·
        refine ⟨11918928421855369379507239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63567618249895303357371941 11918928421855369379507239)
        ·
          refine ⟨17878392632783054069260859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11918928421855369379507239 17878392632783054069260859)
          ·
            refine ⟨26817588949174581103891289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17878392632783054069260859 26817588949174581103891289)
            ·
              refine ⟨20113191711880935827918467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26817588949174581103891289 20113191711880935827918467)
              ·
                refine ⟨30169787567821403741877701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20113191711880935827918467 30169787567821403741877701)
                ·
                  refine ⟨5656835168966513201602069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30169787567821403741877701 5656835168966513201602069)
                  ·
                    refine ⟨265164148545305306325097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5656835168966513201602069 265164148545305306325097)
                    ·
                      rfl

theorem cell23_1549216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 4, 6].length) (baseStart_1549216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1549216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1549216 prefixEnd_1549216 := by exact prefixLift 1549216
  have htrace : WordTrace (prefixWord ++ tailWord_1549216) baseStart_1549216 baseEnd_1549216 := by
    simpa [prefixWord, tailWord_1549216, baseEnd_1549216] using wordTrace_append hprefix tailTrace_1549216
  have hstable : (prefixWord ++ tailWord_1549216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549216).length < 2 ^ (prefixWord ++ tailWord_1549216).sum := by decide
  have hdescent : baseEnd_1549216 < baseStart_1549216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549238 : List Nat := [5, 1, 4, 1, 1, 2, 1, 2, 1, 2, 3]
def baseStart_1549238 : Nat := 118140960795 + 1549238 * 2 ^ 59
def prefixEnd_1549238 : Nat := 4983230072969 + 3 ^ 40 * 1549238 * 2
def baseEnd_1549238 : Nat := 795503742210314832900191

theorem tailTrace_1549238 : CollatzResearch.WordTrace tailWord_1549238 prefixEnd_1549238 795503742210314832900191 := by
  unfold tailWord_1549238
  simp only [CollatzResearch.WordTrace]
  refine ⟨3531584497586424351907523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37670234640921859753680245 3531584497586424351907523)
  ·
    refine ⟨5297376746379636527861285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3531584497586424351907523 5297376746379636527861285)
    ·
      refine ⟨993258139946181848973991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5297376746379636527861285 993258139946181848973991)
      ·
        refine ⟨1489887209919272773460987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 993258139946181848973991 1489887209919272773460987)
        ·
          refine ⟨2234830814878909160191481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1489887209919272773460987 2234830814878909160191481)
          ·
            refine ⟨1676123111159181870143611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2234830814878909160191481 1676123111159181870143611)
            ·
              refine ⟨2514184666738772805215417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1676123111159181870143611 2514184666738772805215417)
              ·
                refine ⟨1885638500054079603911563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2514184666738772805215417 1885638500054079603911563)
                ·
                  refine ⟨2828457750081119405867345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1885638500054079603911563 2828457750081119405867345)
                  ·
                    refine ⟨2121343312560839554400509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2828457750081119405867345 2121343312560839554400509)
                    ·
                      refine ⟨795503742210314832900191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2121343312560839554400509 795503742210314832900191)
                      ·
                        rfl

theorem cell23_1549238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_1549238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1549238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1549238 prefixEnd_1549238 := by exact prefixLift 1549238
  have htrace : WordTrace (prefixWord ++ tailWord_1549238) baseStart_1549238 baseEnd_1549238 := by
    simpa [prefixWord, tailWord_1549238, baseEnd_1549238] using wordTrace_append hprefix tailTrace_1549238
  have hstable : (prefixWord ++ tailWord_1549238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549238).length < 2 ^ (prefixWord ++ tailWord_1549238).sum := by decide
  have hdescent : baseEnd_1549238 < baseStart_1549238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549274 : List Nat := [3, 1, 1, 2, 4, 2, 2, 2, 2, 2, 2]
def baseStart_1549274 : Nat := 118140960795 + 1549274 * 2 ^ 59
def prefixEnd_1549274 : Nat := 4983230072969 + 3 ^ 40 * 1549274 * 2
def baseEnd_1549274 : Nat := 795522227513876692050025

theorem tailTrace_1549274 : CollatzResearch.WordTrace tailWord_1549274 prefixEnd_1549274 795522227513876692050025 := by
  unfold tailWord_1549274
  simp only [CollatzResearch.WordTrace]
  refine ⟨14126666247313091944707719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37671109992834911852553917 14126666247313091944707719)
  ·
    refine ⟨21189999370969637917061579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14126666247313091944707719 21189999370969637917061579)
    ·
      refine ⟨31784999056454456875592369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21189999370969637917061579 31784999056454456875592369)
      ·
        refine ⟨23838749292340842656694277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31784999056454456875592369 23838749292340842656694277)
        ·
          refine ⟨4469765492313907998130177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23838749292340842656694277 4469765492313907998130177)
          ·
            refine ⟨3352324119235430998597633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4469765492313907998130177 3352324119235430998597633)
            ·
              refine ⟨2514243089426573248948225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3352324119235430998597633 2514243089426573248948225)
              ·
                refine ⟨1885682317069929936711169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2514243089426573248948225 1885682317069929936711169)
                ·
                  refine ⟨1414261737802447452533377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1885682317069929936711169 1414261737802447452533377)
                  ·
                    refine ⟨1060696303351835589400033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1414261737802447452533377 1060696303351835589400033)
                    ·
                      refine ⟨795522227513876692050025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1060696303351835589400033 795522227513876692050025)
                      ·
                        rfl

theorem cell23_1549274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 2, 2, 2, 2].length) (baseStart_1549274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1549274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1549274 prefixEnd_1549274 := by exact prefixLift 1549274
  have htrace : WordTrace (prefixWord ++ tailWord_1549274) baseStart_1549274 baseEnd_1549274 := by
    simpa [prefixWord, tailWord_1549274, baseEnd_1549274] using wordTrace_append hprefix tailTrace_1549274
  have hstable : (prefixWord ++ tailWord_1549274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549274).length < 2 ^ (prefixWord ++ tailWord_1549274).sum := by decide
  have hdescent : baseEnd_1549274 < baseStart_1549274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549290 : List Nat := [3, 1, 3, 1, 2, 3, 1, 1, 2, 3, 3]
def baseStart_1549290 : Nat := 118140960795 + 1549290 * 2 ^ 59
def prefixEnd_1549290 : Nat := 4983230072969 + 3 ^ 40 * 1549290 * 2
def baseEnd_1549290 : Nat := 795530443204348629449951

theorem tailTrace_1549290 : CollatzResearch.WordTrace tailWord_1549290 prefixEnd_1549290 795530443204348629449951 := by
  unfold tailWord_1549290
  simp only [CollatzResearch.WordTrace]
  refine ⟨14126812139298600627853331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37671499038129601674275549 14126812139298600627853331)
  ·
    refine ⟨21190218208947900941779997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14126812139298600627853331 21190218208947900941779997)
    ·
      refine ⟨7946331828355462853167499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21190218208947900941779997 7946331828355462853167499)
      ·
        refine ⟨11919497742533194279751249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7946331828355462853167499 11919497742533194279751249)
        ·
          refine ⟨8939623306899895709813437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11919497742533194279751249 8939623306899895709813437)
          ·
            refine ⟨3352358740087460891180039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8939623306899895709813437 3352358740087460891180039)
            ·
              refine ⟨5028538110131191336770059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3352358740087460891180039 5028538110131191336770059)
              ·
                refine ⟨7542807165196787005155089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5028538110131191336770059 7542807165196787005155089)
                ·
                  refine ⟨5657105373897590253866317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7542807165196787005155089 5657105373897590253866317)
                  ·
                    refine ⟨2121414515211596345199869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5657105373897590253866317 2121414515211596345199869)
                    ·
                      refine ⟨795530443204348629449951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2121414515211596345199869 795530443204348629449951)
                      ·
                        rfl

theorem cell23_1549290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_1549290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1549290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1549290 prefixEnd_1549290 := by exact prefixLift 1549290
  have htrace : WordTrace (prefixWord ++ tailWord_1549290) baseStart_1549290 baseEnd_1549290 := by
    simpa [prefixWord, tailWord_1549290, baseEnd_1549290] using wordTrace_append hprefix tailTrace_1549290
  have hstable : (prefixWord ++ tailWord_1549290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549290).length < 2 ^ (prefixWord ++ tailWord_1549290).sum := by decide
  have hdescent : baseEnd_1549290 < baseStart_1549290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549363 : List Nat := [1, 1, 1, 2, 4, 1, 1, 1, 1, 7, 3]
def baseStart_1549363 : Nat := 118140960795 + 1549363 * 2 ^ 59
def prefixEnd_1549363 : Nat := 4983230072969 + 3 ^ 40 * 1549363 * 2
def baseEnd_1549363 : Nat := 795567927292126843837115

theorem tailTrace_1549363 : CollatzResearch.WordTrace tailWord_1549363 prefixEnd_1549363 795567927292126843837115 := by
  unfold tailWord_1549363
  simp only [CollatzResearch.WordTrace]
  refine ⟨56509911085929935978820743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37673274057286623985880495 56509911085929935978820743)
  ·
    refine ⟨84764866628894903968231115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56509911085929935978820743 84764866628894903968231115)
    ·
      refine ⟨127147299943342355952346673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84764866628894903968231115 127147299943342355952346673)
      ·
        refine ⟨95360474957506766964260005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127147299943342355952346673 95360474957506766964260005)
        ·
          refine ⟨17880089054532518805798751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95360474957506766964260005 17880089054532518805798751)
          ·
            refine ⟨26820133581798778208698127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17880089054532518805798751 26820133581798778208698127)
            ·
              refine ⟨40230200372698167313047191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26820133581798778208698127 40230200372698167313047191)
              ·
                refine ⟨60345300559047250969570787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40230200372698167313047191 60345300559047250969570787)
                ·
                  refine ⟨90517950838570876454356181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60345300559047250969570787 90517950838570876454356181)
                  ·
                    refine ⟨2121514472779004916898973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 90517950838570876454356181 2121514472779004916898973)
                    ·
                      refine ⟨795567927292126843837115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2121514472779004916898973 795567927292126843837115)
                      ·
                        rfl

theorem cell23_1549363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 7, 3].length) (baseStart_1549363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1549363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1549363 prefixEnd_1549363 := by exact prefixLift 1549363
  have htrace : WordTrace (prefixWord ++ tailWord_1549363) baseStart_1549363 baseEnd_1549363 := by
    simpa [prefixWord, tailWord_1549363, baseEnd_1549363] using wordTrace_append hprefix tailTrace_1549363
  have hstable : (prefixWord ++ tailWord_1549363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549363).length < 2 ^ (prefixWord ++ tailWord_1549363).sum := by decide
  have hdescent : baseEnd_1549363 < baseStart_1549363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549417 : List Nat := [1, 2, 1, 1, 1, 8, 1, 2, 1, 5]
def baseStart_1549417 : Nat := 118140960795 + 1549417 * 2 ^ 59
def prefixEnd_1549417 : Nat := 4983230072969 + 3 ^ 40 * 1549417 * 2
def baseEnd_1549417 : Nat := 265198551749156544187289

theorem tailTrace_1549417 : CollatzResearch.WordTrace tailWord_1549417 prefixEnd_1549417 265198551749156544187289 := by
  unfold tailWord_1549417
  simp only [CollatzResearch.WordTrace]
  refine ⟨56511880627734303201286505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37674587085156202134191003 56511880627734303201286505)
  ·
    refine ⟨42383910470800727400964879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56511880627734303201286505 42383910470800727400964879)
    ·
      refine ⟨63575865706201091101447319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42383910470800727400964879 63575865706201091101447319)
      ·
        refine ⟨95363798559301636652170979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63575865706201091101447319 95363798559301636652170979)
        ·
          refine ⟨143045697838952454978256469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95363798559301636652170979 143045697838952454978256469)
          ·
            refine ⟨1676316771550224081776443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 143045697838952454978256469 1676316771550224081776443)
            ·
              refine ⟨2514475157325336122664665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1676316771550224081776443 2514475157325336122664665)
              ·
                refine ⟨1885856367994002091998499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2514475157325336122664665 1885856367994002091998499)
                ·
                  refine ⟨2828784551991003137997749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1885856367994002091998499 2828784551991003137997749)
                  ·
                    refine ⟨265198551749156544187289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2828784551991003137997749 265198551749156544187289)
                    ·
                      rfl

theorem cell23_1549417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 2, 1, 5].length) (baseStart_1549417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1549417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1549417 prefixEnd_1549417 := by exact prefixLift 1549417
  have htrace : WordTrace (prefixWord ++ tailWord_1549417) baseStart_1549417 baseEnd_1549417 := by
    simpa [prefixWord, tailWord_1549417, baseEnd_1549417] using wordTrace_append hprefix tailTrace_1549417
  have hstable : (prefixWord ++ tailWord_1549417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549417).length < 2 ^ (prefixWord ++ tailWord_1549417).sum := by decide
  have hdescent : baseEnd_1549417 < baseStart_1549417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549420 : List Nat := [2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 4]
def baseStart_1549420 : Nat := 118140960795 + 1549420 * 2 ^ 59
def prefixEnd_1549420 : Nat := 4983230072969 + 3 ^ 40 * 1549420 * 2
def baseEnd_1549420 : Nat := 795597195689433120824353

theorem tailTrace_1549420 : CollatzResearch.WordTrace tailWord_1549420 prefixEnd_1549420 795597195689433120824353 := by
  unfold tailWord_1549420
  simp only [CollatzResearch.WordTrace]
  refine ⟨28255995023361717356822857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37674660031148956475763809 28255995023361717356822857)
  ·
    refine ⟨21191996267521288017617143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28255995023361717356822857 21191996267521288017617143)
    ·
      refine ⟨31787994401281932026425715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21191996267521288017617143 31787994401281932026425715)
      ·
        refine ⟨47681991601922898039638573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31787994401281932026425715 47681991601922898039638573)
        ·
          refine ⟨17880746850721086764864465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47681991601922898039638573 17880746850721086764864465)
          ·
            refine ⟨13410560138040815073648349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17880746850721086764864465 13410560138040815073648349)
            ·
              refine ⟨5028960051765305652618131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13410560138040815073648349 5028960051765305652618131)
              ·
                refine ⟨7543440077647958478927197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5028960051765305652618131 7543440077647958478927197)
                ·
                  refine ⟨2828790029117984429597699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7543440077647958478927197 2828790029117984429597699)
                  ·
                    refine ⟨4243185043676976644396549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2828790029117984429597699 4243185043676976644396549)
                    ·
                      refine ⟨795597195689433120824353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4243185043676976644396549 795597195689433120824353)
                      ·
                        rfl

theorem cell23_1549420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 4].length) (baseStart_1549420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1549420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1549420 prefixEnd_1549420 := by exact prefixLift 1549420
  have htrace : WordTrace (prefixWord ++ tailWord_1549420) baseStart_1549420 baseEnd_1549420 := by
    simpa [prefixWord, tailWord_1549420, baseEnd_1549420] using wordTrace_append hprefix tailTrace_1549420
  have hstable : (prefixWord ++ tailWord_1549420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549420).length < 2 ^ (prefixWord ++ tailWord_1549420).sum := by decide
  have hdescent : baseEnd_1549420 < baseStart_1549420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549440 : List Nat := [2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 5]
def baseStart_1549440 : Nat := 118140960795 + 1549440 * 2 ^ 59
def prefixEnd_1549440 : Nat := 4983230072969 + 3 ^ 40 * 1549440 * 2
def baseEnd_1549440 : Nat := 795607465302523042574261

theorem tailTrace_1549440 : CollatzResearch.WordTrace tailWord_1549440 prefixEnd_1549440 795607465302523042574261 := by
  unfold tailWord_1549440
  simp only [CollatzResearch.WordTrace]
  refine ⟨28256359753325489064686887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37675146337767318752915849 28256359753325489064686887)
  ·
    refine ⟨42384539629988233597030331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28256359753325489064686887 42384539629988233597030331)
    ·
      refine ⟨63576809444982350395545497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42384539629988233597030331 63576809444982350395545497)
      ·
        refine ⟨47682607083736762796659123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63576809444982350395545497 47682607083736762796659123)
        ·
          refine ⟨71523910625605144194988685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47682607083736762796659123 71523910625605144194988685)
          ·
            refine ⟨26821466484601929073120757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71523910625605144194988685 26821466484601929073120757)
            ·
              refine ⟨2514512482931430850605071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26821466484601929073120757 2514512482931430850605071)
              ·
                refine ⟨3771768724397146275907607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2514512482931430850605071 3771768724397146275907607)
                ·
                  refine ⟨5657653086595719413861411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3771768724397146275907607 5657653086595719413861411)
                  ·
                    refine ⟨8486479629893579120792117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5657653086595719413861411 8486479629893579120792117)
                    ·
                      refine ⟨795607465302523042574261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8486479629893579120792117 795607465302523042574261)
                      ·
                        rfl

theorem cell23_1549440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 5].length) (baseStart_1549440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1549440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1549440 prefixEnd_1549440 := by exact prefixLift 1549440
  have htrace : WordTrace (prefixWord ++ tailWord_1549440) baseStart_1549440 baseEnd_1549440 := by
    simpa [prefixWord, tailWord_1549440, baseEnd_1549440] using wordTrace_append hprefix tailTrace_1549440
  have hstable : (prefixWord ++ tailWord_1549440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549440).length < 2 ^ (prefixWord ++ tailWord_1549440).sum := by decide
  have hdescent : baseEnd_1549440 < baseStart_1549440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549450 : List Nat := [3, 1, 2, 3, 1, 1, 1, 2, 3, 2, 4]
def baseStart_1549450 : Nat := 118140960795 + 1549450 * 2 ^ 59
def prefixEnd_1549450 : Nat := 4983230072969 + 3 ^ 40 * 1549450 * 2
def baseEnd_1549450 : Nat := 795612600109068003449215

theorem tailTrace_1549450 : CollatzResearch.WordTrace tailWord_1549450 prefixEnd_1549450 795612600109068003449215 := by
  unfold tailWord_1549450
  simp only [CollatzResearch.WordTrace]
  refine ⟨14128271059153687459309451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37675389491076499891491869 14128271059153687459309451)
  ·
    refine ⟨21192406588730531188964177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14128271059153687459309451 21192406588730531188964177)
    ·
      refine ⟨15894304941547898391723133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21192406588730531188964177 15894304941547898391723133)
      ·
        refine ⟨5960364353080461896896175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15894304941547898391723133 5960364353080461896896175)
        ·
          refine ⟨8940546529620692845344263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5960364353080461896896175 8940546529620692845344263)
          ·
            refine ⟨13410819794431039268016395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8940546529620692845344263 13410819794431039268016395)
            ·
              refine ⟨20116229691646558902024593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13410819794431039268016395 20116229691646558902024593)
              ·
                refine ⟨15087172268734919176518445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20116229691646558902024593 15087172268734919176518445)
                ·
                  refine ⟨5657689600775594691194417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15087172268734919176518445 5657689600775594691194417)
                  ·
                    refine ⟨4243267200581696018395813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5657689600775594691194417 4243267200581696018395813)
                    ·
                      refine ⟨795612600109068003449215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4243267200581696018395813 795612600109068003449215)
                      ·
                        rfl

theorem cell23_1549450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_1549450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1549450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1549450 prefixEnd_1549450 := by exact prefixLift 1549450
  have htrace : WordTrace (prefixWord ++ tailWord_1549450) baseStart_1549450 baseEnd_1549450 := by
    simpa [prefixWord, tailWord_1549450, baseEnd_1549450] using wordTrace_append hprefix tailTrace_1549450
  have hstable : (prefixWord ++ tailWord_1549450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549450).length < 2 ^ (prefixWord ++ tailWord_1549450).sum := by decide
  have hdescent : baseEnd_1549450 < baseStart_1549450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549471 : List Nat := [1, 1, 2, 6, 2, 1, 1, 2, 3, 2, 2]
def baseStart_1549471 : Nat := 118140960795 + 1549471 * 2 ^ 59
def prefixEnd_1549471 : Nat := 4983230072969 + 3 ^ 40 * 1549471 * 2
def baseEnd_1549471 : Nat := 795623383202812421286619

theorem tailTrace_1549471 : CollatzResearch.WordTrace tailWord_1549471 prefixEnd_1549471 795623383202812421286619 := by
  unfold tailWord_1549471
  simp only [CollatzResearch.WordTrace]
  refine ⟨56513850169538670423752267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37675900113025780282501511 56513850169538670423752267)
  ·
    refine ⟨84770775254308005635628401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56513850169538670423752267 84770775254308005635628401)
    ·
      refine ⟨63578081440731004226721301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84770775254308005635628401 63578081440731004226721301)
      ·
        refine ⟨2980222567534265823127561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 63578081440731004226721301 2980222567534265823127561)
        ·
          refine ⟨2235166925650699367345671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2980222567534265823127561 2235166925650699367345671)
          ·
            refine ⟨3352750388476049051018507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2235166925650699367345671 3352750388476049051018507)
            ·
              refine ⟨5029125582714073576527761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3352750388476049051018507 5029125582714073576527761)
              ·
                refine ⟨3771844187035555182395821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5029125582714073576527761 3771844187035555182395821)
                ·
                  refine ⟨1414441570138333193398433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3771844187035555182395821 1414441570138333193398433)
                  ·
                    refine ⟨1060831177603749895048825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1414441570138333193398433 1060831177603749895048825)
                    ·
                      refine ⟨795623383202812421286619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1060831177603749895048825 795623383202812421286619)
                      ·
                        rfl

theorem cell23_1549471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_1549471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1549471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1549471 prefixEnd_1549471 := by exact prefixLift 1549471
  have htrace : WordTrace (prefixWord ++ tailWord_1549471) baseStart_1549471 baseEnd_1549471 := by
    simpa [prefixWord, tailWord_1549471, baseEnd_1549471] using wordTrace_append hprefix tailTrace_1549471
  have hstable : (prefixWord ++ tailWord_1549471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549471).length < 2 ^ (prefixWord ++ tailWord_1549471).sum := by decide
  have hdescent : baseEnd_1549471 < baseStart_1549471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549494 : List Nat := [5, 1, 3, 2, 1, 1, 10]
def baseStart_1549494 : Nat := 118140960795 + 1549494 * 2 ^ 59
def prefixEnd_1549494 : Nat := 4983230072969 + 3 ^ 40 * 1549494 * 2
def baseEnd_1549494 : Nat := 9822656706887232485173

theorem tailTrace_1549494 : CollatzResearch.WordTrace tailWord_1549494 prefixEnd_1549494 9822656706887232485173 := by
  unfold tailWord_1549494
  simp only [CollatzResearch.WordTrace]
  refine ⟨3532168065528459084489971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37676459365636896901226357 3532168065528459084489971)
  ·
    refine ⟨5298252098292688626734957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3532168065528459084489971 5298252098292688626734957)
    ·
      refine ⟨1986844536859758235025609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5298252098292688626734957 1986844536859758235025609)
      ·
        refine ⟨1490133402644818676269207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1986844536859758235025609 1490133402644818676269207)
        ·
          refine ⟨2235200103967228014403811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1490133402644818676269207 2235200103967228014403811)
          ·
            refine ⟨3352800155950842021605717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2235200103967228014403811 3352800155950842021605717)
            ·
              refine ⟨9822656706887232485173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3352800155950842021605717 9822656706887232485173)
              ·
                rfl

theorem cell23_1549494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 10].length) (baseStart_1549494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1549494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1549494 prefixEnd_1549494 := by exact prefixLift 1549494
  have htrace : WordTrace (prefixWord ++ tailWord_1549494) baseStart_1549494 baseEnd_1549494 := by
    simpa [prefixWord, tailWord_1549494, baseEnd_1549494] using wordTrace_append hprefix tailTrace_1549494
  have hstable : (prefixWord ++ tailWord_1549494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549494).length < 2 ^ (prefixWord ++ tailWord_1549494).sum := by decide
  have hdescent : baseEnd_1549494 < baseStart_1549494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549504 : List Nat := [2, 1, 1, 2, 6, 1, 1, 1, 4, 1, 3]
def baseStart_1549504 : Nat := 118140960795 + 1549504 * 2 ^ 59
def prefixEnd_1549504 : Nat := 4983230072969 + 3 ^ 40 * 1549504 * 2
def baseEnd_1549504 : Nat := 795640328064410792173967

theorem tailTrace_1549504 : CollatzResearch.WordTrace tailWord_1549504 prefixEnd_1549504 795640328064410792173967 := by
  unfold tailWord_1549504
  simp only [CollatzResearch.WordTrace]
  refine ⟨28257526889209558529851783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37676702518946078039802377 28257526889209558529851783)
  ·
    refine ⟨42386290333814337794777675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28257526889209558529851783 42386290333814337794777675)
    ·
      refine ⟨63579435500721506692166513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42386290333814337794777675 63579435500721506692166513)
      ·
        refine ⟨47684576625541130019124885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63579435500721506692166513 47684576625541130019124885)
        ·
          refine ⟨2235214529322240469646479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 47684576625541130019124885 2235214529322240469646479)
          ·
            refine ⟨3352821793983360704469719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2235214529322240469646479 3352821793983360704469719)
            ·
              refine ⟨5029232690975041056704579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3352821793983360704469719 5029232690975041056704579)
              ·
                refine ⟨7543849036462561585056869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5029232690975041056704579 7543849036462561585056869)
                ·
                  refine ⟨1414471694336730297198163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7543849036462561585056869 1414471694336730297198163)
                  ·
                    refine ⟨2121707541505095445797245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1414471694336730297198163 2121707541505095445797245)
                    ·
                      refine ⟨795640328064410792173967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2121707541505095445797245 795640328064410792173967)
                      ·
                        rfl

theorem cell23_1549504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 4, 1, 3].length) (baseStart_1549504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1549504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1549504 prefixEnd_1549504 := by exact prefixLift 1549504
  have htrace : WordTrace (prefixWord ++ tailWord_1549504) baseStart_1549504 baseEnd_1549504 := by
    simpa [prefixWord, tailWord_1549504, baseEnd_1549504] using wordTrace_append hprefix tailTrace_1549504
  have hstable : (prefixWord ++ tailWord_1549504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549504).length < 2 ^ (prefixWord ++ tailWord_1549504).sum := by decide
  have hdescent : baseEnd_1549504 < baseStart_1549504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549530 : List Nat := [3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 5]
def baseStart_1549530 : Nat := 118140960795 + 1549530 * 2 ^ 59
def prefixEnd_1549530 : Nat := 4983230072969 + 3 ^ 40 * 1549530 * 2
def baseEnd_1549530 : Nat := 795653678561427690448847

theorem tailTrace_1549530 : CollatzResearch.WordTrace tailWord_1549530 prefixEnd_1549530 795653678561427690448847 := by
  unfold tailWord_1549530
  simp only [CollatzResearch.WordTrace]
  refine ⟨14129000519081230875037511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37677334717549949000100029 14129000519081230875037511)
  ·
    refine ⟨21193500778621846312556267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14129000519081230875037511 21193500778621846312556267)
    ·
      refine ⟨31790251167932769468834401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21193500778621846312556267 31790251167932769468834401)
      ·
        refine ⟨23842688375949577101625801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31790251167932769468834401 23842688375949577101625801)
        ·
          refine ⟨17882016281962182826219351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23842688375949577101625801 17882016281962182826219351)
          ·
            refine ⟨26823024422943274239329027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17882016281962182826219351 26823024422943274239329027)
            ·
              refine ⟨40234536634414911358993541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26823024422943274239329027 40234536634414911358993541)
              ·
                refine ⟨7543975618952795879811289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40234536634414911358993541 7543975618952795879811289)
                ·
                  refine ⟨5657981714214596909858467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7543975618952795879811289 5657981714214596909858467)
                  ·
                    refine ⟨8486972571321895364787701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5657981714214596909858467 8486972571321895364787701)
                    ·
                      refine ⟨795653678561427690448847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8486972571321895364787701 795653678561427690448847)
                      ·
                        rfl

theorem cell23_1549530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_1549530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1549530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1549530 prefixEnd_1549530 := by exact prefixLift 1549530
  have htrace : WordTrace (prefixWord ++ tailWord_1549530) baseStart_1549530 baseEnd_1549530 := by
    simpa [prefixWord, tailWord_1549530, baseEnd_1549530] using wordTrace_append hprefix tailTrace_1549530
  have hstable : (prefixWord ++ tailWord_1549530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549530).length < 2 ^ (prefixWord ++ tailWord_1549530).sum := by decide
  have hdescent : baseEnd_1549530 < baseStart_1549530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549540 : List Nat := [2, 3, 1, 1, 1, 2, 2, 2, 1, 4, 4]
def baseStart_1549540 : Nat := 118140960795 + 1549540 * 2 ^ 59
def prefixEnd_1549540 : Nat := 4983230072969 + 3 ^ 40 * 1549540 * 2
def baseEnd_1549540 : Nat := 795658813367972651323801

theorem tailTrace_1549540 : CollatzResearch.WordTrace tailWord_1549540 prefixEnd_1549540 795658813367972651323801 := by
  unfold tailWord_1549540
  simp only [CollatzResearch.WordTrace]
  refine ⟨28258183403144347604007037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37677577870859130138676049 28258183403144347604007037)
  ·
    refine ⟨10596818776179130351502639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28258183403144347604007037 10596818776179130351502639)
    ·
      refine ⟨15895228164268695527253959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10596818776179130351502639 15895228164268695527253959)
      ·
        refine ⟨23842842246403043290880939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15895228164268695527253959 23842842246403043290880939)
        ·
          refine ⟨35764263369604564936321409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23842842246403043290880939 35764263369604564936321409)
          ·
            refine ⟨26823197527203423702241057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35764263369604564936321409 26823197527203423702241057)
            ·
              refine ⟨20117398145402567776680793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26823197527203423702241057 20117398145402567776680793)
              ·
                refine ⟨15088048609051925832510595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20117398145402567776680793 15088048609051925832510595)
                ·
                  refine ⟨22632072913577888748765893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15088048609051925832510595 22632072913577888748765893)
                  ·
                    refine ⟨4243513671295854140393605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22632072913577888748765893 4243513671295854140393605)
                    ·
                      refine ⟨795658813367972651323801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4243513671295854140393605 795658813367972651323801)
                      ·
                        rfl

theorem cell23_1549540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_1549540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1549540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1549540 prefixEnd_1549540 := by exact prefixLift 1549540
  have htrace : WordTrace (prefixWord ++ tailWord_1549540) baseStart_1549540 baseEnd_1549540 := by
    simpa [prefixWord, tailWord_1549540, baseEnd_1549540] using wordTrace_append hprefix tailTrace_1549540
  have hstable : (prefixWord ++ tailWord_1549540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549540).length < 2 ^ (prefixWord ++ tailWord_1549540).sum := by decide
  have hdescent : baseEnd_1549540 < baseStart_1549540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549544 : List Nat := [2, 1, 4, 1, 2, 1, 1, 1, 6, 2, 2]
def baseStart_1549544 : Nat := 118140960795 + 1549544 * 2 ^ 59
def prefixEnd_1549544 : Nat := 4983230072969 + 3 ^ 40 * 1549544 * 2
def baseEnd_1549544 : Nat := 795660867290590635673783

theorem tailTrace_1549544 : CollatzResearch.WordTrace tailWord_1549544 prefixEnd_1549544 795660867290590635673783 := by
  unfold tailWord_1549544
  simp only [CollatzResearch.WordTrace]
  refine ⟨28258256349137101945579843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37677675132182802594106457 28258256349137101945579843)
  ·
    refine ⟨42387384523705652918369765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28258256349137101945579843 42387384523705652918369765)
    ·
      refine ⟨7947634598194809922194331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42387384523705652918369765 7947634598194809922194331)
      ·
        refine ⟨11921451897292214883291497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7947634598194809922194331 11921451897292214883291497)
        ·
          refine ⟨8941088922969161162468623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11921451897292214883291497 8941088922969161162468623)
          ·
            refine ⟨13411633384453741743702935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8941088922969161162468623 13411633384453741743702935)
            ·
              refine ⟨20117450076680612615554403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13411633384453741743702935 20117450076680612615554403)
              ·
                refine ⟨30176175115020918923331605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20117450076680612615554403 30176175115020918923331605)
                ·
                  refine ⟨1414508208516605574531169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 30176175115020918923331605 1414508208516605574531169)
                  ·
                    refine ⟨1060881156387454180898377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1414508208516605574531169 1060881156387454180898377)
                    ·
                      refine ⟨795660867290590635673783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1060881156387454180898377 795660867290590635673783)
                      ·
                        rfl

theorem cell23_1549544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 6, 2, 2].length) (baseStart_1549544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1549544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1549544 prefixEnd_1549544 := by exact prefixLift 1549544
  have htrace : WordTrace (prefixWord ++ tailWord_1549544) baseStart_1549544 baseEnd_1549544 := by
    simpa [prefixWord, tailWord_1549544, baseEnd_1549544] using wordTrace_append hprefix tailTrace_1549544
  have hstable : (prefixWord ++ tailWord_1549544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549544).length < 2 ^ (prefixWord ++ tailWord_1549544).sum := by decide
  have hdescent : baseEnd_1549544 < baseStart_1549544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549550 : List Nat := [4, 1, 2, 1, 1, 1, 2, 2, 9]
def baseStart_1549550 : Nat := 118140960795 + 1549550 * 2 ^ 59
def prefixEnd_1549550 : Nat := 4983230072969 + 3 ^ 40 * 1549550 * 2
def baseEnd_1549550 : Nat := 88407105352724179133195

theorem tailTrace_1549550 : CollatzResearch.WordTrace tailWord_1549550 prefixEnd_1549550 88407105352724179133195 := by
  unfold tailWord_1549550
  simp only [CollatzResearch.WordTrace]
  refine ⟨7064591442031558364484763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37677821024168311277252069 7064591442031558364484763)
  ·
    refine ⟨10596887163047337546727145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7064591442031558364484763 10596887163047337546727145)
    ·
      refine ⟨7947665372285503160045359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10596887163047337546727145 7947665372285503160045359)
      ·
        refine ⟨11921498058428254740068039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7947665372285503160045359 11921498058428254740068039)
        ·
          refine ⟨17882247087642382110102059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11921498058428254740068039 17882247087642382110102059)
          ·
            refine ⟨26823370631463573165153089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17882247087642382110102059 26823370631463573165153089)
            ·
              refine ⟨20117527973597679873864817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26823370631463573165153089 20117527973597679873864817)
              ·
                refine ⟨15088145980198259905398613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20117527973597679873864817 15088145980198259905398613)
                ·
                  refine ⟨88407105352724179133195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 15088145980198259905398613 88407105352724179133195)
                  ·
                    rfl

theorem cell23_1549550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 9].length) (baseStart_1549550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1549550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1549550 prefixEnd_1549550 := by exact prefixLift 1549550
  have htrace : WordTrace (prefixWord ++ tailWord_1549550) baseStart_1549550 baseEnd_1549550 := by
    simpa [prefixWord, tailWord_1549550, baseEnd_1549550] using wordTrace_append hprefix tailTrace_1549550
  have hstable : (prefixWord ++ tailWord_1549550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549550).length < 2 ^ (prefixWord ++ tailWord_1549550).sum := by decide
  have hdescent : baseEnd_1549550 < baseStart_1549550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549567 : List Nat := [1, 1, 2, 2, 1, 7, 1, 1, 7]
def baseStart_1549567 : Nat := 118140960795 + 1549567 * 2 ^ 59
def prefixEnd_1549567 : Nat := 4983230072969 + 3 ^ 40 * 1549567 * 2
def baseEnd_1549567 : Nat := 88408075260627116187353

theorem tailTrace_1549567 : CollatzResearch.WordTrace tailWord_1549567 prefixEnd_1549567 88408075260627116187353 := by
  unfold tailWord_1549567
  simp only [CollatzResearch.WordTrace]
  refine ⟨56517351577190878819246955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37678234384793919212831303 56517351577190878819246955)
  ·
    refine ⟨84776027365786318228870433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56517351577190878819246955 84776027365786318228870433)
    ·
      refine ⟨63582020524339738671652825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84776027365786318228870433 63582020524339738671652825)
      ·
        refine ⟨47686515393254804003739619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63582020524339738671652825 47686515393254804003739619)
        ·
          refine ⟨71529773089882206005609429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47686515393254804003739619 71529773089882206005609429)
          ·
            refine ⟨1676479056794114203256471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 71529773089882206005609429 1676479056794114203256471)
            ·
              refine ⟨2514718585191171304884707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1676479056794114203256471 2514718585191171304884707)
              ·
                refine ⟨3772077877786756957327061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2514718585191171304884707 3772077877786756957327061)
                ·
                  refine ⟨88408075260627116187353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3772077877786756957327061 88408075260627116187353)
                  ·
                    rfl

theorem cell23_1549567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 1, 7].length) (baseStart_1549567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1549567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1549567 prefixEnd_1549567 := by exact prefixLift 1549567
  have htrace : WordTrace (prefixWord ++ tailWord_1549567) baseStart_1549567 baseEnd_1549567 := by
    simpa [prefixWord, tailWord_1549567, baseEnd_1549567] using wordTrace_append hprefix tailTrace_1549567
  have hstable : (prefixWord ++ tailWord_1549567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549567).length < 2 ^ (prefixWord ++ tailWord_1549567).sum := by decide
  have hdescent : baseEnd_1549567 < baseStart_1549567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549637 : List Nat := [1, 3, 1, 1, 1, 2, 1, 4, 4, 2, 3]
def baseStart_1549637 : Nat := 118140960795 + 1549637 * 2 ^ 59
def prefixEnd_1549637 : Nat := 4983230072969 + 3 ^ 40 * 1549637 * 2
def baseEnd_1549637 : Nat := 795708620991458771810855

theorem tailTrace_1549637 : CollatzResearch.WordTrace tailWord_1549637 prefixEnd_1549637 795708620991458771810855 := by
  unfold tailWord_1549637
  simp only [CollatzResearch.WordTrace]
  refine ⟨56519904686937280774295165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37679936457958187182863443 56519904686937280774295165)
  ·
    refine ⟨21194964257601480290360687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56519904686937280774295165 21194964257601480290360687)
    ·
      refine ⟨31792446386402220435541031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21194964257601480290360687 31792446386402220435541031)
      ·
        refine ⟨47688669579603330653311547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31792446386402220435541031 47688669579603330653311547)
        ·
          refine ⟨71533004369404995979967321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47688669579603330653311547 71533004369404995979967321)
          ·
            refine ⟨53649753277053746984975491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71533004369404995979967321 53649753277053746984975491)
            ·
              refine ⟨80474629915580620477463237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53649753277053746984975491 80474629915580620477463237)
              ·
                refine ⟨15088993109171366339524357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80474629915580620477463237 15088993109171366339524357)
                ·
                  refine ⟨2829186207969631188660817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15088993109171366339524357 2829186207969631188660817)
                  ·
                    refine ⟨2121889655977223391495613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2829186207969631188660817 2121889655977223391495613)
                    ·
                      refine ⟨795708620991458771810855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2121889655977223391495613 795708620991458771810855)
                      ·
                        rfl

theorem cell23_1549637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 4, 2, 3].length) (baseStart_1549637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1549637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1549637 prefixEnd_1549637 := by exact prefixLift 1549637
  have htrace : WordTrace (prefixWord ++ tailWord_1549637) baseStart_1549637 baseEnd_1549637 := by
    simpa [prefixWord, tailWord_1549637, baseEnd_1549637] using wordTrace_append hprefix tailTrace_1549637
  have hstable : (prefixWord ++ tailWord_1549637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549637).length < 2 ^ (prefixWord ++ tailWord_1549637).sum := by decide
  have hdescent : baseEnd_1549637 < baseStart_1549637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549640 : List Nat := [2, 1, 3, 1, 1, 2, 1, 2, 10]
def baseStart_1549640 : Nat := 118140960795 + 1549640 * 2 ^ 59
def prefixEnd_1549640 : Nat := 4983230072969 + 3 ^ 40 * 1549640 * 2
def baseEnd_1549640 : Nat := 88412240159269140008149

theorem tailTrace_1549640 : CollatzResearch.WordTrace tailWord_1549640 prefixEnd_1549640 88412240159269140008149 := by
  unfold tailWord_1549640
  simp only [CollatzResearch.WordTrace]
  refine ⟨28260007052963206143327187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37680009403950941524436249 28260007052963206143327187)
  ·
    refine ⟨42390010579444809214990781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28260007052963206143327187 42390010579444809214990781)
    ·
      refine ⟨15896253967291803455621543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42390010579444809214990781 15896253967291803455621543)
      ·
        refine ⟨23844380950937705183432315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15896253967291803455621543 23844380950937705183432315)
        ·
          refine ⟨35766571426406557775148473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23844380950937705183432315 35766571426406557775148473)
          ·
            refine ⟨26824928569804918331361355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35766571426406557775148473 26824928569804918331361355)
            ·
              refine ⟨40237392854707377497042033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26824928569804918331361355 40237392854707377497042033)
              ·
                refine ⟨30178044641030533122781525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40237392854707377497042033 30178044641030533122781525)
                ·
                  refine ⟨88412240159269140008149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 30178044641030533122781525 88412240159269140008149)
                  ·
                    rfl

theorem cell23_1549640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 10].length) (baseStart_1549640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1549640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1549640 prefixEnd_1549640 := by exact prefixLift 1549640
  have htrace : WordTrace (prefixWord ++ tailWord_1549640) baseStart_1549640 baseEnd_1549640 := by
    simpa [prefixWord, tailWord_1549640, baseEnd_1549640] using wordTrace_append hprefix tailTrace_1549640
  have hstable : (prefixWord ++ tailWord_1549640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549640).length < 2 ^ (prefixWord ++ tailWord_1549640).sum := by decide
  have hdescent : baseEnd_1549640 < baseStart_1549640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549644 : List Nat := [2, 2, 1, 3, 2, 3, 1, 2, 3, 4]
def baseStart_1549644 : Nat := 118140960795 + 1549644 * 2 ^ 59
def prefixEnd_1549644 : Nat := 4983230072969 + 3 ^ 40 * 1549644 * 2
def baseEnd_1549644 : Nat := 265237405118680081474441

theorem tailTrace_1549644 : CollatzResearch.WordTrace tailWord_1549644 prefixEnd_1549644 265237405118680081474441 := by
  unfold tailWord_1549644
  simp only [CollatzResearch.WordTrace]
  refine ⟨28260079998955960484899993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37680106665274613979866657 28260079998955960484899993)
  ·
    refine ⟨21195059999216970363674995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28260079998955960484899993 21195059999216970363674995)
    ·
      refine ⟨31792589998825455545512493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21195059999216970363674995 31792589998825455545512493)
      ·
        refine ⟨11922221249559545829567185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31792589998825455545512493 11922221249559545829567185)
        ·
          refine ⟨8941665937169659372175389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11922221249559545829567185 8941665937169659372175389)
          ·
            refine ⟨3353124726438622264565771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8941665937169659372175389 3353124726438622264565771)
            ·
              refine ⟨5029687089657933396848657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3353124726438622264565771 5029687089657933396848657)
              ·
                refine ⟨3772265317243450047636493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5029687089657933396848657 3772265317243450047636493)
                ·
                  refine ⟨1414599493966293767863685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3772265317243450047636493 1414599493966293767863685)
                  ·
                    refine ⟨265237405118680081474441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1414599493966293767863685 265237405118680081474441)
                    ·
                      rfl

theorem cell23_1549644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 2, 3, 4].length) (baseStart_1549644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1549644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1549644 prefixEnd_1549644 := by exact prefixLift 1549644
  have htrace : WordTrace (prefixWord ++ tailWord_1549644) baseStart_1549644 baseEnd_1549644 := by
    simpa [prefixWord, tailWord_1549644, baseEnd_1549644] using wordTrace_append hprefix tailTrace_1549644
  have hstable : (prefixWord ++ tailWord_1549644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549644).length < 2 ^ (prefixWord ++ tailWord_1549644).sum := by decide
  have hdescent : baseEnd_1549644 < baseStart_1549644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549674 : List Nat := [3, 1, 3, 3, 2, 1, 1, 1, 8]
def baseStart_1549674 : Nat := 118140960795 + 1549674 * 2 ^ 59
def prefixEnd_1549674 : Nat := 4983230072969 + 3 ^ 40 * 1549674 * 2
def baseEnd_1549674 : Nat := 88414179975075014116465

theorem tailTrace_1549674 : CollatzResearch.WordTrace tailWord_1549674 prefixEnd_1549674 88414179975075014116465 := by
  unfold tailWord_1549674
  simp only [CollatzResearch.WordTrace]
  refine ⟨14130313546950809023348019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37680836125202157395594717 14130313546950809023348019)
  ·
    refine ⟨21195470320426213535022029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14130313546950809023348019 21195470320426213535022029)
    ·
      refine ⟨7948301370159830075633261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21195470320426213535022029 7948301370159830075633261)
      ·
        refine ⟨2980613013809936278362473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7948301370159830075633261 2980613013809936278362473)
        ·
          refine ⟨2235459760357452208771855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2980613013809936278362473 2235459760357452208771855)
          ·
            refine ⟨3353189640536178313157783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2235459760357452208771855 3353189640536178313157783)
            ·
              refine ⟨5029784460804267469736675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3353189640536178313157783 5029784460804267469736675)
              ·
                refine ⟨7544676691206401204605013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5029784460804267469736675 7544676691206401204605013)
                ·
                  refine ⟨88414179975075014116465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7544676691206401204605013 88414179975075014116465)
                  ·
                    rfl

theorem cell23_1549674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 8].length) (baseStart_1549674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1549674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1549674 prefixEnd_1549674 := by exact prefixLift 1549674
  have htrace : WordTrace (prefixWord ++ tailWord_1549674) baseStart_1549674 baseEnd_1549674 := by
    simpa [prefixWord, tailWord_1549674, baseEnd_1549674] using wordTrace_append hprefix tailTrace_1549674
  have hstable : (prefixWord ++ tailWord_1549674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549674).length < 2 ^ (prefixWord ++ tailWord_1549674).sum := by decide
  have hdescent : baseEnd_1549674 < baseStart_1549674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549677 : List Nat := [1, 5, 1, 1, 1, 3, 1, 1, 1, 2, 6]
def baseStart_1549677 : Nat := 118140960795 + 1549677 * 2 ^ 59
def prefixEnd_1549677 : Nat := 4983230072969 + 3 ^ 40 * 1549677 * 2
def baseEnd_1549677 : Nat := 795729160217638615310671

theorem tailTrace_1549677 : CollatzResearch.WordTrace tailWord_1549677 prefixEnd_1549677 795729160217638615310671 := by
  unfold tailWord_1549677
  simp only [CollatzResearch.WordTrace]
  refine ⟨56521363606792367605751285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37680909071194911737167523 56521363606792367605751285)
  ·
    refine ⟨5298877838136784463039183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56521363606792367605751285 5298877838136784463039183)
    ·
      refine ⟨7948316757205176694558775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5298877838136784463039183 7948316757205176694558775)
      ·
        refine ⟨11922475135807765041838163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7948316757205176694558775 11922475135807765041838163)
        ·
          refine ⟨17883712703711647562757245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11922475135807765041838163 17883712703711647562757245)
          ·
            refine ⟨6706392263891867836033967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17883712703711647562757245 6706392263891867836033967)
            ·
              refine ⟨10059588395837801754050951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6706392263891867836033967 10059588395837801754050951)
              ·
                refine ⟨15089382593756702631076427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10059588395837801754050951 15089382593756702631076427)
                ·
                  refine ⟨22634073890635053946614641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15089382593756702631076427 22634073890635053946614641)
                  ·
                    refine ⟨16975555417976290459960981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22634073890635053946614641 16975555417976290459960981)
                    ·
                      refine ⟨795729160217638615310671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16975555417976290459960981 795729160217638615310671)
                      ·
                        rfl

theorem cell23_1549677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_1549677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1549677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1549677 prefixEnd_1549677 := by exact prefixLift 1549677
  have htrace : WordTrace (prefixWord ++ tailWord_1549677) baseStart_1549677 baseEnd_1549677 := by
    simpa [prefixWord, tailWord_1549677, baseEnd_1549677] using wordTrace_append hprefix tailTrace_1549677
  have hstable : (prefixWord ++ tailWord_1549677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549677).length < 2 ^ (prefixWord ++ tailWord_1549677).sum := by decide
  have hdescent : baseEnd_1549677 < baseStart_1549677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549678 : List Nat := [4, 1, 2, 4, 1, 1, 2, 1, 3, 4]
def baseStart_1549678 : Nat := 118140960795 + 1549678 * 2 ^ 59
def prefixEnd_1549678 : Nat := 4983230072969 + 3 ^ 40 * 1549678 * 2
def baseEnd_1549678 : Nat := 265243224566097703799389

theorem tailTrace_1549678 : CollatzResearch.WordTrace tailWord_1549678 prefixEnd_1549678 265243224566097703799389 := by
  unfold tailWord_1549678
  simp only [CollatzResearch.WordTrace]
  refine ⟨7065175009973593097067211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37680933386525829851025125 7065175009973593097067211)
  ·
    refine ⟨10597762514960389645600817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7065175009973593097067211 10597762514960389645600817)
    ·
      refine ⟨7948321886220292234200613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10597762514960389645600817 7948321886220292234200613)
      ·
        refine ⟨1490310353666304793912615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7948321886220292234200613 1490310353666304793912615)
        ·
          refine ⟨2235465530499457190868923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1490310353666304793912615 2235465530499457190868923)
          ·
            refine ⟨3353198295749185786303385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2235465530499457190868923 3353198295749185786303385)
            ·
              refine ⟨2514898721811889339727539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3353198295749185786303385 2514898721811889339727539)
              ·
                refine ⟨3772348082717834009591309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2514898721811889339727539 3772348082717834009591309)
                ·
                  refine ⟨1414630531019187753596741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3772348082717834009591309 1414630531019187753596741)
                  ·
                    refine ⟨265243224566097703799389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1414630531019187753596741 265243224566097703799389)
                    ·
                      rfl

theorem cell23_1549678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_1549678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1549678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1549678 prefixEnd_1549678 := by exact prefixLift 1549678
  have htrace : WordTrace (prefixWord ++ tailWord_1549678) baseStart_1549678 baseEnd_1549678 := by
    simpa [prefixWord, tailWord_1549678, baseEnd_1549678] using wordTrace_append hprefix tailTrace_1549678
  have hstable : (prefixWord ++ tailWord_1549678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549678).length < 2 ^ (prefixWord ++ tailWord_1549678).sum := by decide
  have hdescent : baseEnd_1549678 < baseStart_1549678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549704 : List Nat := [2, 1, 3, 3, 1, 2, 1, 4, 1, 5]
def baseStart_1549704 : Nat := 118140960795 + 1549704 * 2 ^ 59
def prefixEnd_1549704 : Nat := 4983230072969 + 3 ^ 40 * 1549704 * 2
def baseEnd_1549704 : Nat := 265247674731770003224349

theorem tailTrace_1549704 : CollatzResearch.WordTrace tailWord_1549704 prefixEnd_1549704 265247674731770003224349 := by
  unfold tailWord_1549704
  simp only [CollatzResearch.WordTrace]
  refine ⟨28261174188847275608492083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37681565585129700811322777 28261174188847275608492083)
  ·
    refine ⟨42391761283270913412738125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28261174188847275608492083 42391761283270913412738125)
    ·
      refine ⟨15896910481226592529776797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42391761283270913412738125 15896910481226592529776797)
      ·
        refine ⟨5961341430459972198666299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15896910481226592529776797 5961341430459972198666299)
        ·
          refine ⟨8942012145689958297999449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5961341430459972198666299 8942012145689958297999449)
          ·
            refine ⟨6706509109267468723499587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8942012145689958297999449 6706509109267468723499587)
            ·
              refine ⟨10059763663901203085249381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6706509109267468723499587 10059763663901203085249381)
              ·
                refine ⟨1886205686981475578484259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10059763663901203085249381 1886205686981475578484259)
                ·
                  refine ⟨2829308530472213367726389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1886205686981475578484259 2829308530472213367726389)
                  ·
                    refine ⟨265247674731770003224349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2829308530472213367726389 265247674731770003224349)
                    ·
                      rfl

theorem cell23_1549704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 4, 1, 5].length) (baseStart_1549704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1549704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1549704 prefixEnd_1549704 := by exact prefixLift 1549704
  have htrace : WordTrace (prefixWord ++ tailWord_1549704) baseStart_1549704 baseEnd_1549704 := by
    simpa [prefixWord, tailWord_1549704, baseEnd_1549704] using wordTrace_append hprefix tailTrace_1549704
  have hstable : (prefixWord ++ tailWord_1549704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549704).length < 2 ^ (prefixWord ++ tailWord_1549704).sum := by decide
  have hdescent : baseEnd_1549704 < baseStart_1549704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549717 : List Nat := [1, 3, 2, 1, 1, 2, 2, 4, 1, 6]
def baseStart_1549717 : Nat := 118140960795 + 1549717 * 2 ^ 59
def prefixEnd_1549717 : Nat := 4983230072969 + 3 ^ 40 * 1549717 * 2
def baseEnd_1549717 : Nat := 265249899814606152936829

theorem tailTrace_1549717 : CollatzResearch.WordTrace tailWord_1549717 prefixEnd_1549717 265249899814606152936829 := by
  unfold tailWord_1549717
  simp only [CollatzResearch.WordTrace]
  refine ⟨56522822526647454437207405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37681881684431636291471603 56522822526647454437207405)
  ·
    refine ⟨21196058447492795413952777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56522822526647454437207405 21196058447492795413952777)
    ·
      refine ⟨15897043835619596560464583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21196058447492795413952777 15897043835619596560464583)
      ·
        refine ⟨23845565753429394840696875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15897043835619596560464583 23845565753429394840696875)
        ·
          refine ⟨35768348630144092261045313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23845565753429394840696875 35768348630144092261045313)
          ·
            refine ⟨26826261472608069195783985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35768348630144092261045313 26826261472608069195783985)
            ·
              refine ⟨20119696104456051896837989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26826261472608069195783985 20119696104456051896837989)
              ·
                refine ⟨3772443019585509730657123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20119696104456051896837989 3772443019585509730657123)
                ·
                  refine ⟨5658664529378264595985685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3772443019585509730657123 5658664529378264595985685)
                  ·
                    refine ⟨265249899814606152936829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5658664529378264595985685 265249899814606152936829)
                    ·
                      rfl

theorem cell23_1549717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4, 1, 6].length) (baseStart_1549717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1549717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1549717 prefixEnd_1549717 := by exact prefixLift 1549717
  have htrace : WordTrace (prefixWord ++ tailWord_1549717) baseStart_1549717 baseEnd_1549717 := by
    simpa [prefixWord, tailWord_1549717, baseEnd_1549717] using wordTrace_append hprefix tailTrace_1549717
  have hstable : (prefixWord ++ tailWord_1549717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549717).length < 2 ^ (prefixWord ++ tailWord_1549717).sum := by decide
  have hdescent : baseEnd_1549717 < baseStart_1549717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549735 : List Nat := [1, 1, 6, 1, 1, 1, 5, 2, 1, 1, 3]
def baseStart_1549735 : Nat := 118140960795 + 1549735 * 2 ^ 59
def prefixEnd_1549735 : Nat := 4983230072969 + 3 ^ 40 * 1549735 * 2
def baseEnd_1549735 : Nat := 795758942095599388385405

theorem tailTrace_1549735 : CollatzResearch.WordTrace tailWord_1549735 prefixEnd_1549735 795758942095599388385405 := by
  unfold tailWord_1549735
  simp only [CollatzResearch.WordTrace]
  refine ⟨56523479040582243511362659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37682319360388162340908439 56523479040582243511362659)
  ·
    refine ⟨84785218560873365267043989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56523479040582243511362659 84785218560873365267043989)
    ·
      refine ⟨3974307120040938996892687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 84785218560873365267043989 3974307120040938996892687)
      ·
        refine ⟨5961460680061408495339031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3974307120040938996892687 5961460680061408495339031)
        ·
          refine ⟨8942191020092112743008547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5961460680061408495339031 8942191020092112743008547)
          ·
            refine ⟨13413286530138169114512821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8942191020092112743008547 13413286530138169114512821)
            ·
              refine ⟨1257495612200453354485577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13413286530138169114512821 1257495612200453354485577)
              ·
                refine ⟨943121709150340015864183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1257495612200453354485577 943121709150340015864183)
                ·
                  refine ⟨1414682563725510023796275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 943121709150340015864183 1414682563725510023796275)
                  ·
                    refine ⟨2122023845588265035694413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1414682563725510023796275 2122023845588265035694413)
                    ·
                      refine ⟨795758942095599388385405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2122023845588265035694413 795758942095599388385405)
                      ·
                        rfl

theorem cell23_1549735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_1549735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1549735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1549735 prefixEnd_1549735 := by exact prefixLift 1549735
  have htrace : WordTrace (prefixWord ++ tailWord_1549735) baseStart_1549735 baseEnd_1549735 := by
    simpa [prefixWord, tailWord_1549735, baseEnd_1549735] using wordTrace_append hprefix tailTrace_1549735
  have hstable : (prefixWord ++ tailWord_1549735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549735).length < 2 ^ (prefixWord ++ tailWord_1549735).sum := by decide
  have hdescent : baseEnd_1549735 < baseStart_1549735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549764 : List Nat := [2, 3, 3, 2, 1, 1, 2, 9]
def baseStart_1549764 : Nat := 118140960795 + 1549764 * 2 ^ 59
def prefixEnd_1549764 : Nat := 4983230072969 + 3 ^ 40 * 1549764 * 2
def baseEnd_1549764 : Nat := 29473104927206658330473

theorem tailTrace_1549764 : CollatzResearch.WordTrace tailWord_1549764 prefixEnd_1549764 29473104927206658330473 := by
  unfold tailWord_1549764
  simp only [CollatzResearch.WordTrace]
  refine ⟨28262268378738590732084173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37683024504984787642778897 28262268378738590732084173)
  ·
    refine ⟨10598350642026971524531565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28262268378738590732084173 10598350642026971524531565)
    ·
      refine ⟨3974381490760114321699337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10598350642026971524531565 3974381490760114321699337)
      ·
        refine ⟨2980786118070085741274503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3974381490760114321699337 2980786118070085741274503)
        ·
          refine ⟨4471179177105128611911755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2980786118070085741274503 4471179177105128611911755)
          ·
            refine ⟨6706768765657692917867633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4471179177105128611911755 6706768765657692917867633)
            ·
              refine ⟨5030076574243269688400725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6706768765657692917867633 5030076574243269688400725)
              ·
                refine ⟨29473104927206658330473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5030076574243269688400725 29473104927206658330473)
                ·
                  rfl

theorem cell23_1549764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 9].length) (baseStart_1549764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1549764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1549764 prefixEnd_1549764 := by exact prefixLift 1549764
  have htrace : WordTrace (prefixWord ++ tailWord_1549764) baseStart_1549764 baseEnd_1549764 := by
    simpa [prefixWord, tailWord_1549764, baseEnd_1549764] using wordTrace_append hprefix tailTrace_1549764
  have hstable : (prefixWord ++ tailWord_1549764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549764).length < 2 ^ (prefixWord ++ tailWord_1549764).sum := by decide
  have hdescent : baseEnd_1549764 < baseStart_1549764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549774 : List Nat := [4, 1, 1, 1, 2, 1, 3, 1, 3, 3, 3]
def baseStart_1549774 : Nat := 118140960795 + 1549774 * 2 ^ 59
def prefixEnd_1549774 : Nat := 4983230072969 + 3 ^ 40 * 1549774 * 2
def baseEnd_1549774 : Nat := 795778967841124735797725

theorem tailTrace_1549774 : CollatzResearch.WordTrace tailWord_1549774 prefixEnd_1549774 795778967841124735797725 := by
  unfold tailWord_1549774
  simp only [CollatzResearch.WordTrace]
  refine ⟨7065612685930119146504047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37683267658293968781354917 7065612685930119146504047)
  ·
    refine ⟨10598419028895178719756071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7065612685930119146504047 10598419028895178719756071)
    ·
      refine ⟨15897628543342768079634107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10598419028895178719756071 15897628543342768079634107)
      ·
        refine ⟨23846442815014152119451161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15897628543342768079634107 23846442815014152119451161)
        ·
          refine ⟨17884832111260614089588371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23846442815014152119451161 17884832111260614089588371)
          ·
            refine ⟨26827248166890921134382557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17884832111260614089588371 26827248166890921134382557)
            ·
              refine ⟨10060218062584095425393459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26827248166890921134382557 10060218062584095425393459)
              ·
                refine ⟨15090327093876143138090189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10060218062584095425393459 15090327093876143138090189)
                ·
                  refine ⟨5658872660203553676783821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15090327093876143138090189 5658872660203553676783821)
                  ·
                    refine ⟨2122077247576332628793933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5658872660203553676783821 2122077247576332628793933)
                    ·
                      refine ⟨795778967841124735797725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2122077247576332628793933 795778967841124735797725)
                      ·
                        rfl

theorem cell23_1549774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 3, 3, 3].length) (baseStart_1549774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1549774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1549774 prefixEnd_1549774 := by exact prefixLift 1549774
  have htrace : WordTrace (prefixWord ++ tailWord_1549774) baseStart_1549774 baseEnd_1549774 := by
    simpa [prefixWord, tailWord_1549774, baseEnd_1549774] using wordTrace_append hprefix tailTrace_1549774
  have hstable : (prefixWord ++ tailWord_1549774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549774).length < 2 ^ (prefixWord ++ tailWord_1549774).sum := by decide
  have hdescent : baseEnd_1549774 < baseStart_1549774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549807 : List Nat := [1, 1, 2, 1, 4, 1, 3, 1, 1, 8]
def baseStart_1549807 : Nat := 118140960795 + 1549807 * 2 ^ 59
def prefixEnd_1549807 : Nat := 4983230072969 + 3 ^ 40 * 1549807 * 2
def baseEnd_1549807 : Nat := 265265304234241035561691

theorem tailTrace_1549807 : CollatzResearch.WordTrace tailWord_1549807 prefixEnd_1549807 265265304234241035561691 := by
  unfold tailWord_1549807
  simp only [CollatzResearch.WordTrace]
  refine ⟨56526105096321399807983675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37684070064214266538655783 56526105096321399807983675)
  ·
    refine ⟨84789157644482099711975513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56526105096321399807983675 84789157644482099711975513)
    ·
      refine ⟨63591868233361574783981635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84789157644482099711975513 63591868233361574783981635)
      ·
        refine ⟨95387802350042362175972453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63591868233361574783981635 95387802350042362175972453)
        ·
          refine ⟨17885212940632942907994835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95387802350042362175972453 17885212940632942907994835)
          ·
            refine ⟨26827819410949414361992253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17885212940632942907994835 26827819410949414361992253)
            ·
              refine ⟨10060432279106030385747095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26827819410949414361992253 10060432279106030385747095)
              ·
                refine ⟨15090648418659045578620643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10060432279106030385747095 15090648418659045578620643)
                ·
                  refine ⟨22635972627988568367930965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15090648418659045578620643 22635972627988568367930965)
                  ·
                    refine ⟨265265304234241035561691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 22635972627988568367930965 265265304234241035561691)
                    ·
                      rfl

theorem cell23_1549807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 8].length) (baseStart_1549807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1549807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1549807 prefixEnd_1549807 := by exact prefixLift 1549807
  have htrace : WordTrace (prefixWord ++ tailWord_1549807) baseStart_1549807 baseEnd_1549807 := by
    simpa [prefixWord, tailWord_1549807, baseEnd_1549807] using wordTrace_append hprefix tailTrace_1549807
  have hstable : (prefixWord ++ tailWord_1549807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549807).length < 2 ^ (prefixWord ++ tailWord_1549807).sum := by decide
  have hdescent : baseEnd_1549807 < baseStart_1549807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549921 : List Nat := [1, 2, 3, 1, 1, 3, 2, 1, 1, 6, 2]
def baseStart_1549921 : Nat := 118140960795 + 1549921 * 2 ^ 59
def prefixEnd_1549921 : Nat := 4983230072969 + 3 ^ 40 * 1549921 * 2
def baseEnd_1549921 : Nat := 795854449497335660659549

theorem tailTrace_1549921 : CollatzResearch.WordTrace tailWord_1549921 prefixEnd_1549921 795854449497335660659549 := by
  unfold tailWord_1549921
  simp only [CollatzResearch.WordTrace]
  refine ⟨56530263017908397277633617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37686842011938931518422411 56530263017908397277633617)
  ·
    refine ⟨42397697263431297958225213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56530263017908397277633617 42397697263431297958225213)
    ·
      refine ⟨15899136473786736734334455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42397697263431297958225213 15899136473786736734334455)
      ·
        refine ⟨23848704710680105101501683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15899136473786736734334455 23848704710680105101501683)
        ·
          refine ⟨35773057066020157652252525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23848704710680105101501683 35773057066020157652252525)
          ·
            refine ⟨13414896399757559119594697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35773057066020157652252525 13414896399757559119594697)
            ·
              refine ⟨10061172299818169339696023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13414896399757559119594697 10061172299818169339696023)
              ·
                refine ⟨15091758449727254009544035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10061172299818169339696023 15091758449727254009544035)
                ·
                  refine ⟨22637637674590881014316053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15091758449727254009544035 22637637674590881014316053)
                  ·
                    refine ⟨1061139265996447547546065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22637637674590881014316053 1061139265996447547546065)
                    ·
                      refine ⟨795854449497335660659549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1061139265996447547546065 795854449497335660659549)
                      ·
                        rfl

theorem cell23_1549921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 6, 2].length) (baseStart_1549921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1549921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1549921 prefixEnd_1549921 := by exact prefixLift 1549921
  have htrace : WordTrace (prefixWord ++ tailWord_1549921) baseStart_1549921 baseEnd_1549921 := by
    simpa [prefixWord, tailWord_1549921, baseEnd_1549921] using wordTrace_append hprefix tailTrace_1549921
  have hstable : (prefixWord ++ tailWord_1549921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549921).length < 2 ^ (prefixWord ++ tailWord_1549921).sum := by decide
  have hdescent : baseEnd_1549921 < baseStart_1549921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549938 : List Nat := [3, 2, 1, 2, 3, 2, 2, 1, 2, 1, 4]
def baseStart_1549938 : Nat := 118140960795 + 1549938 * 2 ^ 59
def prefixEnd_1549938 : Nat := 4983230072969 + 3 ^ 40 * 1549938 * 2
def baseEnd_1549938 : Nat := 795863178668462094146971

theorem tailTrace_1549938 : CollatzResearch.WordTrace tailWord_1549938 prefixEnd_1549938 795863178668462094146971 := by
  unfold tailWord_1549938
  simp only [CollatzResearch.WordTrace]
  refine ⟨14132720764711702295250617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37687255372564539454001645 14132720764711702295250617)
  ·
    refine ⟨10599540573533776721437963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14132720764711702295250617 10599540573533776721437963)
    ·
      refine ⟨15899310860300665082156945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10599540573533776721437963 15899310860300665082156945)
      ·
        refine ⟨11924483145225498811617709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15899310860300665082156945 11924483145225498811617709)
        ·
          refine ⟨4471681179459562054356641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11924483145225498811617709 4471681179459562054356641)
          ·
            refine ⟨3353760884594671540767481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4471681179459562054356641 3353760884594671540767481)
            ·
              refine ⟨2515320663446003655575611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3353760884594671540767481 2515320663446003655575611)
              ·
                refine ⟨3772980995169005483363417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2515320663446003655575611 3772980995169005483363417)
                ·
                  refine ⟨2829735746376754112522563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3772980995169005483363417 2829735746376754112522563)
                  ·
                    refine ⟨4244603619565131168783845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2829735746376754112522563 4244603619565131168783845)
                    ·
                      refine ⟨795863178668462094146971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4244603619565131168783845 795863178668462094146971)
                      ·
                        rfl

theorem cell23_1549938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_1549938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1549938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1549938 prefixEnd_1549938 := by exact prefixLift 1549938
  have htrace : WordTrace (prefixWord ++ tailWord_1549938) baseStart_1549938 baseEnd_1549938 := by
    simpa [prefixWord, tailWord_1549938, baseEnd_1549938] using wordTrace_append hprefix tailTrace_1549938
  have hstable : (prefixWord ++ tailWord_1549938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549938).length < 2 ^ (prefixWord ++ tailWord_1549938).sum := by decide
  have hdescent : baseEnd_1549938 < baseStart_1549938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549948 : List Nat := [2, 2, 2, 1, 1, 2, 1, 7, 1, 4]
def baseStart_1549948 : Nat := 118140960795 + 1549948 * 2 ^ 59
def prefixEnd_1549948 : Nat := 4983230072969 + 3 ^ 40 * 1549948 * 2
def baseEnd_1549948 : Nat := 265289437825002351673975

theorem tailTrace_1549948 : CollatzResearch.WordTrace tailWord_1549948 prefixEnd_1549948 265289437825002351673975 := by
  unfold tailWord_1549948
  simp only [CollatzResearch.WordTrace]
  refine ⟨28265623894405290444433249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37687498525873720592577665 28265623894405290444433249)
  ·
    refine ⟨21199217920803967833324937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28265623894405290444433249 21199217920803967833324937)
    ·
      refine ⟨15899413440602975874993703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21199217920803967833324937 15899413440602975874993703)
      ·
        refine ⟨23849120160904463812490555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15899413440602975874993703 23849120160904463812490555)
        ·
          refine ⟨35773680241356695718735833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23849120160904463812490555 35773680241356695718735833)
          ·
            refine ⟨26830260181017521789051875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35773680241356695718735833 26830260181017521789051875)
            ·
              refine ⟨40245390271526282683577813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26830260181017521789051875 40245390271526282683577813)
              ·
                refine ⟨943251334488897250396355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 40245390271526282683577813 943251334488897250396355)
                ·
                  refine ⟨1414877001733345875594533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 943251334488897250396355 1414877001733345875594533)
                  ·
                    refine ⟨265289437825002351673975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1414877001733345875594533 265289437825002351673975)
                    ·
                      rfl

theorem cell23_1549948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 7, 1, 4].length) (baseStart_1549948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1549948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1549948 prefixEnd_1549948 := by exact prefixLift 1549948
  have htrace : WordTrace (prefixWord ++ tailWord_1549948) baseStart_1549948 baseEnd_1549948 := by
    simpa [prefixWord, tailWord_1549948, baseEnd_1549948] using wordTrace_append hprefix tailTrace_1549948
  have hstable : (prefixWord ++ tailWord_1549948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549948).length < 2 ^ (prefixWord ++ tailWord_1549948).sum := by decide
  have hdescent : baseEnd_1549948 < baseStart_1549948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549964 : List Nat := [2, 2, 1, 2, 1, 1, 4, 1, 1, 2, 6]
def baseStart_1549964 : Nat := 118140960795 + 1549964 * 2 ^ 59
def prefixEnd_1549964 : Nat := 4983230072969 + 3 ^ 40 * 1549964 * 2
def baseEnd_1549964 : Nat := 795876529165478992421851

theorem tailTrace_1549964 : CollatzResearch.WordTrace tailWord_1549964 prefixEnd_1549964 795876529165478992421851 := by
  unfold tailWord_1549964
  simp only [CollatzResearch.WordTrace]
  refine ⟨28265915678376307810724473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37687887571168410414299297 28265915678376307810724473)
  ·
    refine ⟨21199436758782230858043355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28265915678376307810724473 21199436758782230858043355)
    ·
      refine ⟨31799155138173346287065033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21199436758782230858043355 31799155138173346287065033)
      ·
        refine ⟨23849366353630009715298775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31799155138173346287065033 23849366353630009715298775)
        ·
          refine ⟨35774049530445014572948163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23849366353630009715298775 35774049530445014572948163)
          ·
            refine ⟨53661074295667521859422245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35774049530445014572948163 53661074295667521859422245)
            ·
              refine ⟨10061451430437660348641671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53661074295667521859422245 10061451430437660348641671)
              ·
                refine ⟨15092177145656490522962507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10061451430437660348641671 15092177145656490522962507)
                ·
                  refine ⟨22638265718484735784443761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15092177145656490522962507 22638265718484735784443761)
                  ·
                    refine ⟨16978699288863551838332821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22638265718484735784443761 16978699288863551838332821)
                    ·
                      refine ⟨795876529165478992421851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16978699288863551838332821 795876529165478992421851)
                      ·
                        rfl

theorem cell23_1549964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_1549964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1549964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1549964 prefixEnd_1549964 := by exact prefixLift 1549964
  have htrace : WordTrace (prefixWord ++ tailWord_1549964) baseStart_1549964 baseEnd_1549964 := by
    simpa [prefixWord, tailWord_1549964, baseEnd_1549964] using wordTrace_append hprefix tailTrace_1549964
  have hstable : (prefixWord ++ tailWord_1549964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549964).length < 2 ^ (prefixWord ++ tailWord_1549964).sum := by decide
  have hdescent : baseEnd_1549964 < baseStart_1549964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549988 : List Nat := [2, 3, 1, 2, 2, 2, 1, 1, 5, 1, 3]
def baseStart_1549988 : Nat := 118140960795 + 1549988 * 2 ^ 59
def prefixEnd_1549988 : Nat := 4983230072969 + 3 ^ 40 * 1549988 * 2
def baseEnd_1549988 : Nat := 795888852701186898521741

theorem tailTrace_1549988 : CollatzResearch.WordTrace tailWord_1549988 prefixEnd_1549988 795888852701186898521741 := by
  unfold tailWord_1549988
  simp only [CollatzResearch.WordTrace]
  refine ⟨28266353354332833860161309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37688471139110445146881745 28266353354332833860161309)
  ·
    refine ⟨10599882507874812697560491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28266353354332833860161309 10599882507874812697560491)
    ·
      refine ⟨15899823761812219046340737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10599882507874812697560491 15899823761812219046340737)
      ·
        refine ⟨11924867821359164284755553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15899823761812219046340737 11924867821359164284755553)
        ·
          refine ⟨8943650866019373213566665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11924867821359164284755553 8943650866019373213566665)
          ·
            refine ⟨6707738149514529910174999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8943650866019373213566665 6707738149514529910174999)
            ·
              refine ⟨10061607224271794865262499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6707738149514529910174999 10061607224271794865262499)
              ·
                refine ⟨15092410836407692297893749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10061607224271794865262499 15092410836407692297893749)
                ·
                  refine ⟨1414913515913221152927539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15092410836407692297893749 1414913515913221152927539)
                  ·
                    refine ⟨2122370273869831729391309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1414913515913221152927539 2122370273869831729391309)
                    ·
                      refine ⟨795888852701186898521741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2122370273869831729391309 795888852701186898521741)
                      ·
                        rfl

theorem cell23_1549988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 5, 1, 3].length) (baseStart_1549988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1549988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1549988 prefixEnd_1549988 := by exact prefixLift 1549988
  have htrace : WordTrace (prefixWord ++ tailWord_1549988) baseStart_1549988 baseEnd_1549988 := by
    simpa [prefixWord, tailWord_1549988, baseEnd_1549988] using wordTrace_append hprefix tailTrace_1549988
  have hstable : (prefixWord ++ tailWord_1549988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549988).length < 2 ^ (prefixWord ++ tailWord_1549988).sum := by decide
  have hdescent : baseEnd_1549988 < baseStart_1549988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549992 : List Nat := [2, 1, 7, 1, 1, 1, 1, 1, 1, 4, 3]
def baseStart_1549992 : Nat := 118140960795 + 1549992 * 2 ^ 59
def prefixEnd_1549992 : Nat := 4983230072969 + 3 ^ 40 * 1549992 * 2
def baseEnd_1549992 : Nat := 795890906623804882871723

theorem tailTrace_1549992 : CollatzResearch.WordTrace tailWord_1549992 prefixEnd_1549992 795890906623804882871723 := by
  unfold tailWord_1549992
  simp only [CollatzResearch.WordTrace]
  refine ⟨28266426300325588201734115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37688568400434117602312153 28266426300325588201734115)
  ·
    refine ⟨42399639450488382302601173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28266426300325588201734115 42399639450488382302601173)
    ·
      refine ⟨993741549620821460217215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 42399639450488382302601173 993741549620821460217215)
      ·
        refine ⟨1490612324431232190325823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 993741549620821460217215 1490612324431232190325823)
        ·
          refine ⟨2235918486646848285488735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1490612324431232190325823 2235918486646848285488735)
          ·
            refine ⟨3353877729970272428233103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2235918486646848285488735 3353877729970272428233103)
            ·
              refine ⟨5030816594955408642349655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3353877729970272428233103 5030816594955408642349655)
              ·
                refine ⟨7546224892433112963524483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5030816594955408642349655 7546224892433112963524483)
                ·
                  refine ⟨11319337338649669445286725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7546224892433112963524483 11319337338649669445286725)
                  ·
                    refine ⟨2122375750996813020991261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11319337338649669445286725 2122375750996813020991261)
                    ·
                      refine ⟨795890906623804882871723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2122375750996813020991261 795890906623804882871723)
                      ·
                        rfl

theorem cell23_1549992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_1549992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1549992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1549992 prefixEnd_1549992 := by exact prefixLift 1549992
  have htrace : WordTrace (prefixWord ++ tailWord_1549992) baseStart_1549992 baseEnd_1549992 := by
    simpa [prefixWord, tailWord_1549992, baseEnd_1549992] using wordTrace_append hprefix tailTrace_1549992
  have hstable : (prefixWord ++ tailWord_1549992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549992).length < 2 ^ (prefixWord ++ tailWord_1549992).sum := by decide
  have hdescent : baseEnd_1549992 < baseStart_1549992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550011 : List Nat := [1, 1, 1, 1, 1, 2, 3, 2, 1, 8, 2]
def baseStart_1550011 : Nat := 118140960795 + 1550011 * 2 ^ 59
def prefixEnd_1550011 : Nat := 4983230072969 + 3 ^ 40 * 1550011 * 2
def baseEnd_1550011 : Nat := 795900662756240308534135

theorem tailTrace_1550011 : CollatzResearch.WordTrace tailWord_1550011 prefixEnd_1550011 795900662756240308534135 := by
  unfold tailWord_1550011
  simp only [CollatzResearch.WordTrace]
  refine ⟨56533545587582342648409887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37689030391721561765606591 56533545587582342648409887)
  ·
    refine ⟨84800318381373513972614831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56533545587582342648409887 84800318381373513972614831)
    ·
      refine ⟨127200477572060270958922247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84800318381373513972614831 127200477572060270958922247)
      ·
        refine ⟨190800716358090406438383371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127200477572060270958922247 190800716358090406438383371)
        ·
          refine ⟨286201074537135609657575057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190800716358090406438383371 286201074537135609657575057)
          ·
            refine ⟨214650805902851707243181293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 286201074537135609657575057 214650805902851707243181293)
            ·
              refine ⟨80494052213569390216192985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 214650805902851707243181293 80494052213569390216192985)
              ·
                refine ⟨60370539160177042662144739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80494052213569390216192985 60370539160177042662144739)
                ·
                  refine ⟨90555808740265563993217109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60370539160177042662144739 90555808740265563993217109)
                  ·
                    refine ⟨1061200883674987078045513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 90555808740265563993217109 1061200883674987078045513)
                    ·
                      refine ⟨795900662756240308534135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1061200883674987078045513 795900662756240308534135)
                      ·
                        rfl

theorem cell23_1550011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 8, 2].length) (baseStart_1550011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1550011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1550011 prefixEnd_1550011 := by exact prefixLift 1550011
  have htrace : WordTrace (prefixWord ++ tailWord_1550011) baseStart_1550011 baseEnd_1550011 := by
    simpa [prefixWord, tailWord_1550011, baseEnd_1550011] using wordTrace_append hprefix tailTrace_1550011
  have hstable : (prefixWord ++ tailWord_1550011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550011).length < 2 ^ (prefixWord ++ tailWord_1550011).sum := by decide
  have hdescent : baseEnd_1550011 < baseStart_1550011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550021 : List Nat := [1, 3, 1, 1, 1, 1, 2, 5, 4, 4]
def baseStart_1550021 : Nat := 118140960795 + 1550021 * 2 ^ 59
def prefixEnd_1550021 : Nat := 4983230072969 + 3 ^ 40 * 1550021 * 2
def baseEnd_1550021 : Nat := 265301932520928423136363

theorem tailTrace_1550021 : CollatzResearch.WordTrace tailWord_1550021 prefixEnd_1550021 265301932520928423136363 := by
  unfold tailWord_1550021
  simp only [CollatzResearch.WordTrace]
  refine ⟨56533910317546114356273917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37689273545030742904182611 56533910317546114356273917)
  ·
    refine ⟨21200216369079792883602719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56533910317546114356273917 21200216369079792883602719)
    ·
      refine ⟨31800324553619689325404079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21200216369079792883602719 31800324553619689325404079)
      ·
        refine ⟨47700486830429533988106119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31800324553619689325404079 47700486830429533988106119)
        ·
          refine ⟨71550730245644300982159179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47700486830429533988106119 71550730245644300982159179)
          ·
            refine ⟨107326095368466451473238769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71550730245644300982159179 107326095368466451473238769)
            ·
              refine ⟨80494571526349838604929077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107326095368466451473238769 80494571526349838604929077)
              ·
                refine ⟨7546366080595297369212101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80494571526349838604929077 7546366080595297369212101)
                ·
                  refine ⟨1414943640111618256727269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7546366080595297369212101 1414943640111618256727269)
                  ·
                    refine ⟨265301932520928423136363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1414943640111618256727269 265301932520928423136363)
                    ·
                      rfl

theorem cell23_1550021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 4, 4].length) (baseStart_1550021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1550021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1550021 prefixEnd_1550021 := by exact prefixLift 1550021
  have htrace : WordTrace (prefixWord ++ tailWord_1550021) baseStart_1550021 baseEnd_1550021 := by
    simpa [prefixWord, tailWord_1550021, baseEnd_1550021] using wordTrace_append hprefix tailTrace_1550021
  have hstable : (prefixWord ++ tailWord_1550021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550021).length < 2 ^ (prefixWord ++ tailWord_1550021).sum := by decide
  have hdescent : baseEnd_1550021 < baseStart_1550021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550031 : List Nat := [1, 1, 2, 1, 1, 3, 1, 3, 5, 2, 3]
def baseStart_1550031 : Nat := 118140960795 + 1550031 * 2 ^ 59
def prefixEnd_1550031 : Nat := 4983230072969 + 3 ^ 40 * 1550031 * 2
def baseEnd_1550031 : Nat := 795910932369330230284043

theorem tailTrace_1550031 : CollatzResearch.WordTrace tailWord_1550031 prefixEnd_1550031 795910932369330230284043 := by
  unfold tailWord_1550031
  simp only [CollatzResearch.WordTrace]
  refine ⟨56534275047509886064137947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37689516698339924042758631 56534275047509886064137947)
  ·
    refine ⟨84801412571264829096206921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56534275047509886064137947 84801412571264829096206921)
    ·
      refine ⟨63601059428448621822155191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84801412571264829096206921 63601059428448621822155191)
      ·
        refine ⟨95401589142672932733232787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63601059428448621822155191 95401589142672932733232787)
        ·
          refine ⟨143102383714009399099849181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95401589142672932733232787 143102383714009399099849181)
          ·
            refine ⟨53663393892753524662443443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143102383714009399099849181 53663393892753524662443443)
            ·
              refine ⟨80495090839130286993665165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53663393892753524662443443 80495090839130286993665165)
              ·
                refine ⟨30185659064673857622624437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80495090839130286993665165 30185659064673857622624437)
                ·
                  refine ⟨2829905537313174152121041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30185659064673857622624437 2829905537313174152121041)
                  ·
                    refine ⟨2122429152984880614090781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2829905537313174152121041 2122429152984880614090781)
                    ·
                      refine ⟨795910932369330230284043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2122429152984880614090781 795910932369330230284043)
                      ·
                        rfl

theorem cell23_1550031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 5, 2, 3].length) (baseStart_1550031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1550031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1550031 prefixEnd_1550031 := by exact prefixLift 1550031
  have htrace : WordTrace (prefixWord ++ tailWord_1550031) baseStart_1550031 baseEnd_1550031 := by
    simpa [prefixWord, tailWord_1550031, baseEnd_1550031] using wordTrace_append hprefix tailTrace_1550031
  have hstable : (prefixWord ++ tailWord_1550031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550031).length < 2 ^ (prefixWord ++ tailWord_1550031).sum := by decide
  have hdescent : baseEnd_1550031 < baseStart_1550031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550041 : List Nat := [1, 2, 1, 2, 3, 4, 1, 1, 1, 1, 6]
def baseStart_1550041 : Nat := 118140960795 + 1550041 * 2 ^ 59
def prefixEnd_1550041 : Nat := 4983230072969 + 3 ^ 40 * 1550041 * 2
def baseEnd_1550041 : Nat := 795916067175875191158997

theorem tailTrace_1550041 : CollatzResearch.WordTrace tailWord_1550041 prefixEnd_1550041 795916067175875191158997 := by
  unfold tailWord_1550041
  simp only [CollatzResearch.WordTrace]
  refine ⟨56534639777473657772001977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37689759851649105181334651 56534639777473657772001977)
  ·
    refine ⟨42400979833105243329001483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56534639777473657772001977 42400979833105243329001483)
    ·
      refine ⟨63601469749657864993502225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42400979833105243329001483 63601469749657864993502225)
      ·
        refine ⟨47701102312243398745126669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63601469749657864993502225 47701102312243398745126669)
        ·
          refine ⟨17887913367091274529422501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47701102312243398745126669 17887913367091274529422501)
          ·
            refine ⟨3353983756329613974266719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17887913367091274529422501 3353983756329613974266719)
            ·
              refine ⟨5030975634494420961400079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3353983756329613974266719 5030975634494420961400079)
              ·
                refine ⟨7546463451741631442100119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5030975634494420961400079 7546463451741631442100119)
                ·
                  refine ⟨11319695177612447163150179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7546463451741631442100119 11319695177612447163150179)
                  ·
                    refine ⟨16979542766418670744725269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11319695177612447163150179 16979542766418670744725269)
                    ·
                      refine ⟨795916067175875191158997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16979542766418670744725269 795916067175875191158997)
                      ·
                        rfl

theorem cell23_1550041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 1, 6].length) (baseStart_1550041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1550041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1550041 prefixEnd_1550041 := by exact prefixLift 1550041
  have htrace : WordTrace (prefixWord ++ tailWord_1550041) baseStart_1550041 baseEnd_1550041 := by
    simpa [prefixWord, tailWord_1550041, baseEnd_1550041] using wordTrace_append hprefix tailTrace_1550041
  have hstable : (prefixWord ++ tailWord_1550041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550041).length < 2 ^ (prefixWord ++ tailWord_1550041).sum := by decide
  have hdescent : baseEnd_1550041 < baseStart_1550041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550048 : List Nat := [2, 1, 1, 3, 1, 2, 3, 4, 1, 2, 3]
def baseStart_1550048 : Nat := 118140960795 + 1550048 * 2 ^ 59
def prefixEnd_1550048 : Nat := 4983230072969 + 3 ^ 40 * 1550048 * 2
def baseEnd_1550048 : Nat := 795919661540456663771465

theorem tailTrace_1550048 : CollatzResearch.WordTrace tailWord_1550048 prefixEnd_1550048 795919661540456663771465 := by
  unfold tailWord_1550048
  simp only [CollatzResearch.WordTrace]
  refine ⟨28267447544224148983753399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37689930058965531978337865 28267447544224148983753399)
  ·
    refine ⟨42401171316336223475630099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28267447544224148983753399 42401171316336223475630099)
    ·
      refine ⟨63601756974504335213445149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42401171316336223475630099 63601756974504335213445149)
      ·
        refine ⟨23850658865439125705041931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63601756974504335213445149 23850658865439125705041931)
        ·
          refine ⟨35775988298158688557562897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23850658865439125705041931 35775988298158688557562897)
          ·
            refine ⟨26831991223619016418172173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35775988298158688557562897 26831991223619016418172173)
            ·
              refine ⟨10061996708857131156814565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26831991223619016418172173 10061996708857131156814565)
              ·
                refine ⟨1886624382910712091902731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10061996708857131156814565 1886624382910712091902731)
                ·
                  refine ⟨2829936574366068137854097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1886624382910712091902731 2829936574366068137854097)
                  ·
                    refine ⟨2122452430774551103390573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2829936574366068137854097 2122452430774551103390573)
                    ·
                      refine ⟨795919661540456663771465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2122452430774551103390573 795919661540456663771465)
                      ·
                        rfl

theorem cell23_1550048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 4, 1, 2, 3].length) (baseStart_1550048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1550048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1550048 prefixEnd_1550048 := by exact prefixLift 1550048
  have htrace : WordTrace (prefixWord ++ tailWord_1550048) baseStart_1550048 baseEnd_1550048 := by
    simpa [prefixWord, tailWord_1550048, baseEnd_1550048] using wordTrace_append hprefix tailTrace_1550048
  have hstable : (prefixWord ++ tailWord_1550048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550048).length < 2 ^ (prefixWord ++ tailWord_1550048).sum := by decide
  have hdescent : baseEnd_1550048 < baseStart_1550048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550093 : List Nat := [1, 7, 2, 1, 2, 1, 1, 2, 1, 5]
def baseStart_1550093 : Nat := 118140960795 + 1550093 * 2 ^ 59
def prefixEnd_1550093 : Nat := 4983230072969 + 3 ^ 40 * 1550093 * 2
def baseEnd_1550093 : Nat := 265314256056636329236253

theorem tailTrace_1550093 : CollatzResearch.WordTrace tailWord_1550093 prefixEnd_1550093 265314256056636329236253 := by
  unfold tailWord_1550093
  simp only [CollatzResearch.WordTrace]
  refine ⟨56536536373285270652894933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37691024248856847101929955 56536536373285270652894933)
  ·
    refine ⟨1325075071248873530927225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 56536536373285270652894933 1325075071248873530927225)
    ·
      refine ⟨993806303436655148195419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1325075071248873530927225 993806303436655148195419)
      ·
        refine ⟨1490709455154982722293129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 993806303436655148195419 1490709455154982722293129)
        ·
          refine ⟨1118032091366237041719847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1490709455154982722293129 1118032091366237041719847)
          ·
            refine ⟨1677048137049355562579771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1118032091366237041719847 1677048137049355562579771)
            ·
              refine ⟨2515572205574033343869657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1677048137049355562579771 2515572205574033343869657)
              ·
                refine ⟨1886679154180525007902243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2515572205574033343869657 1886679154180525007902243)
                ·
                  refine ⟨2830018731270787511853365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1886679154180525007902243 2830018731270787511853365)
                  ·
                    refine ⟨265314256056636329236253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2830018731270787511853365 265314256056636329236253)
                    ·
                      rfl

theorem cell23_1550093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_1550093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1550093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1550093 prefixEnd_1550093 := by exact prefixLift 1550093
  have htrace : WordTrace (prefixWord ++ tailWord_1550093) baseStart_1550093 baseEnd_1550093 := by
    simpa [prefixWord, tailWord_1550093, baseEnd_1550093] using wordTrace_append hprefix tailTrace_1550093
  have hstable : (prefixWord ++ tailWord_1550093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550093).length < 2 ^ (prefixWord ++ tailWord_1550093).sum := by decide
  have hdescent : baseEnd_1550093 < baseStart_1550093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550121 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 3, 6, 3]
def baseStart_1550121 : Nat := 118140960795 + 1550121 * 2 ^ 59
def prefixEnd_1550121 : Nat := 4983230072969 + 3 ^ 40 * 1550121 * 2
def baseEnd_1550121 : Nat := 795957145628234878158629

theorem tailTrace_1550121 : CollatzResearch.WordTrace tailWord_1550121 prefixEnd_1550121 795957145628234878158629 := by
  unfold tailWord_1550121
  simp only [CollatzResearch.WordTrace]
  refine ⟨56537557617183831434914217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37691705078122554289942811 56537557617183831434914217)
  ·
    refine ⟨42403168212887873576185663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56537557617183831434914217 42403168212887873576185663)
    ·
      refine ⟨63604752319331810364278495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42403168212887873576185663 63604752319331810364278495)
      ·
        refine ⟨95407128478997715546417743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63604752319331810364278495 95407128478997715546417743)
        ·
          refine ⟨143110692718496573319626615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95407128478997715546417743 143110692718496573319626615)
          ·
            refine ⟨214666039077744859979439923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143110692718496573319626615 214666039077744859979439923)
            ·
              refine ⟨321999058616617289969159885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214666039077744859979439923 321999058616617289969159885)
              ·
                refine ⟨120749646981231483738434957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 321999058616617289969159885 120749646981231483738434957)
                ·
                  refine ⟨45281117617961806401913109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120749646981231483738434957 45281117617961806401913109)
                  ·
                    refine ⟨2122552388341959675089677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 45281117617961806401913109 2122552388341959675089677)
                    ·
                      refine ⟨795957145628234878158629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2122552388341959675089677 795957145628234878158629)
                      ·
                        rfl

theorem cell23_1550121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 6, 3].length) (baseStart_1550121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1550121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1550121 prefixEnd_1550121 := by exact prefixLift 1550121
  have htrace : WordTrace (prefixWord ++ tailWord_1550121) baseStart_1550121 baseEnd_1550121 := by
    simpa [prefixWord, tailWord_1550121, baseEnd_1550121] using wordTrace_append hprefix tailTrace_1550121
  have hstable : (prefixWord ++ tailWord_1550121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550121).length < 2 ^ (prefixWord ++ tailWord_1550121).sum := by decide
  have hdescent : baseEnd_1550121 < baseStart_1550121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550138 : List Nat := [3, 1, 1, 1, 5, 1, 1, 1, 2, 4, 3]
def baseStart_1550138 : Nat := 118140960795 + 1550138 * 2 ^ 59
def prefixEnd_1550138 : Nat := 4983230072969 + 3 ^ 40 * 1550138 * 2
def baseEnd_1550138 : Nat := 795965874799361311646051

theorem tailTrace_1550138 : CollatzResearch.WordTrace tailWord_1550138 prefixEnd_1550138 795965874799361311646051 := by
  unfold tailWord_1550138
  simp only [CollatzResearch.WordTrace]
  refine ⟨14134544414530560834570767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37692118438748162225522045 14134544414530560834570767)
  ·
    refine ⟨21201816621795841251856151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14134544414530560834570767 21201816621795841251856151)
    ·
      refine ⟨31802724932693761877784227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21201816621795841251856151 31802724932693761877784227)
      ·
        refine ⟨47704087399040642816676341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31802724932693761877784227 47704087399040642816676341)
        ·
          refine ⟨4472258193660060264063407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47704087399040642816676341 4472258193660060264063407)
          ·
            refine ⟨6708387290490090396095111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4472258193660060264063407 6708387290490090396095111)
            ·
              refine ⟨10062580935735135594142667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6708387290490090396095111 10062580935735135594142667)
              ·
                refine ⟨15093871403602703391214001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10062580935735135594142667 15093871403602703391214001)
                ·
                  refine ⟨11320403552702027543410501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15093871403602703391214001 11320403552702027543410501)
                  ·
                    refine ⟨2122575666131630164389469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11320403552702027543410501 2122575666131630164389469)
                    ·
                      refine ⟨795965874799361311646051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2122575666131630164389469 795965874799361311646051)
                      ·
                        rfl

theorem cell23_1550138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 2, 4, 3].length) (baseStart_1550138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1550138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1550138 prefixEnd_1550138 := by exact prefixLift 1550138
  have htrace : WordTrace (prefixWord ++ tailWord_1550138) baseStart_1550138 baseEnd_1550138 := by
    simpa [prefixWord, tailWord_1550138, baseEnd_1550138] using wordTrace_append hprefix tailTrace_1550138
  have hstable : (prefixWord ++ tailWord_1550138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550138).length < 2 ^ (prefixWord ++ tailWord_1550138).sum := by decide
  have hdescent : baseEnd_1550138 < baseStart_1550138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550152 : List Nat := [2, 1, 3, 1, 1, 4, 2, 3, 2, 2, 2]
def baseStart_1550152 : Nat := 118140960795 + 1550152 * 2 ^ 59
def prefixEnd_1550152 : Nat := 4983230072969 + 3 ^ 40 * 1550152 * 2
def baseEnd_1550152 : Nat := 795973063528524256870987

theorem tailTrace_1550152 : CollatzResearch.WordTrace tailWord_1550152 prefixEnd_1550152 795973063528524256870987 := by
  unfold tailWord_1550152
  simp only [CollatzResearch.WordTrace]
  refine ⟨28269344140035761864646355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37692458853381015819528473 28269344140035761864646355)
  ·
    refine ⟨42404016210053642796969533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28269344140035761864646355 42404016210053642796969533)
    ·
      refine ⟨15901506078770116048863575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42404016210053642796969533 15901506078770116048863575)
      ·
        refine ⟨23852259118155174073295363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15901506078770116048863575 23852259118155174073295363)
        ·
          refine ⟨35778388677232761109943045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23852259118155174073295363 35778388677232761109943045)
          ·
            refine ⟨6708447876981142708114321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35778388677232761109943045 6708447876981142708114321)
            ·
              refine ⟨5031335907735857031085741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6708447876981142708114321 5031335907735857031085741)
              ·
                refine ⟨1886750965400946386657153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5031335907735857031085741 1886750965400946386657153)
                ·
                  refine ⟨1415063224050709789992865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1886750965400946386657153 1415063224050709789992865)
                  ·
                    refine ⟨1061297418038032342494649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1415063224050709789992865 1061297418038032342494649)
                    ·
                      refine ⟨795973063528524256870987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1061297418038032342494649 795973063528524256870987)
                      ·
                        rfl

theorem cell23_1550152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 3, 2, 2, 2].length) (baseStart_1550152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1550152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1550152 prefixEnd_1550152 := by exact prefixLift 1550152
  have htrace : WordTrace (prefixWord ++ tailWord_1550152) baseStart_1550152 baseEnd_1550152 := by
    simpa [prefixWord, tailWord_1550152, baseEnd_1550152] using wordTrace_append hprefix tailTrace_1550152
  have hstable : (prefixWord ++ tailWord_1550152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550152).length < 2 ^ (prefixWord ++ tailWord_1550152).sum := by decide
  have hdescent : baseEnd_1550152 < baseStart_1550152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550175 : List Nat := [1, 1, 2, 3, 1, 5, 2, 3, 5]
def baseStart_1550175 : Nat := 118140960795 + 1550175 * 2 ^ 59
def prefixEnd_1550175 : Nat := 4983230072969 + 3 ^ 40 * 1550175 * 2
def baseEnd_1550175 : Nat := 88442763731508629653709

theorem tailTrace_1550175 : CollatzResearch.WordTrace tailWord_1550175 prefixEnd_1550175 88442763731508629653709 := by
  unfold tailWord_1550175
  simp only [CollatzResearch.WordTrace]
  refine ⟨56539527158988198657379979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37693018105992132438253319 56539527158988198657379979)
  ·
    refine ⟨84809290738482297986069969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56539527158988198657379979 84809290738482297986069969)
    ·
      refine ⟨63606968053861723489552477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84809290738482297986069969 63606968053861723489552477)
      ·
        refine ⟨23852613020198146308582179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63606968053861723489552477 23852613020198146308582179)
        ·
          refine ⟨35778919530297219462873269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23852613020198146308582179 35778919530297219462873269)
          ·
            refine ⟨3354273705965364324644369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35778919530297219462873269 3354273705965364324644369)
            ·
              refine ⟨2515705279474023243483277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3354273705965364324644369 2515705279474023243483277)
              ·
                refine ⟨943389479802758716306229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2515705279474023243483277 943389479802758716306229)
                ·
                  refine ⟨88442763731508629653709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 943389479802758716306229 88442763731508629653709)
                  ·
                    rfl

theorem cell23_1550175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 3, 5].length) (baseStart_1550175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1550175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1550175 prefixEnd_1550175 := by exact prefixLift 1550175
  have htrace : WordTrace (prefixWord ++ tailWord_1550175) baseStart_1550175 baseEnd_1550175 := by
    simpa [prefixWord, tailWord_1550175, baseEnd_1550175] using wordTrace_append hprefix tailTrace_1550175
  have hstable : (prefixWord ++ tailWord_1550175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550175).length < 2 ^ (prefixWord ++ tailWord_1550175).sum := by decide
  have hdescent : baseEnd_1550175 < baseStart_1550175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550242 : List Nat := [3, 3, 1, 2, 3, 1, 1, 2, 2, 1, 4]
def baseStart_1550242 : Nat := 118140960795 + 1550242 * 2 ^ 59
def prefixEnd_1550242 : Nat := 4983230072969 + 3 ^ 40 * 1550242 * 2
def baseEnd_1550242 : Nat := 796019276787428904745573

theorem tailTrace_1550242 : CollatzResearch.WordTrace tailWord_1550242 prefixEnd_1550242 796019276787428904745573 := by
  unfold tailWord_1550242
  simp only [CollatzResearch.WordTrace]
  refine ⟨14135492712436367275017245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37694647233163646066712653 14135492712436367275017245)
  ·
    refine ⟨5300809767163637728131467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14135492712436367275017245 5300809767163637728131467)
    ·
      refine ⟨7951214650745456592197201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5300809767163637728131467 7951214650745456592197201)
      ·
        refine ⟨5963410988059092444147901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7951214650745456592197201 5963410988059092444147901)
        ·
          refine ⟨2236279120522159666555463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5963410988059092444147901 2236279120522159666555463)
          ·
            refine ⟨3354418680783239499833195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2236279120522159666555463 3354418680783239499833195)
            ·
              refine ⟨5031628021174859249749793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3354418680783239499833195 5031628021174859249749793)
              ·
                refine ⟨3773721015881144437312345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5031628021174859249749793 3773721015881144437312345)
                ·
                  refine ⟨2830290761910858327984259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3773721015881144437312345 2830290761910858327984259)
                  ·
                    refine ⟨4245436142866287491976389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2830290761910858327984259 4245436142866287491976389)
                    ·
                      refine ⟨796019276787428904745573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4245436142866287491976389 796019276787428904745573)
                      ·
                        rfl

theorem cell23_1550242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_1550242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1550242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1550242 prefixEnd_1550242 := by exact prefixLift 1550242
  have htrace : WordTrace (prefixWord ++ tailWord_1550242) baseStart_1550242 baseEnd_1550242 := by
    simpa [prefixWord, tailWord_1550242, baseEnd_1550242] using wordTrace_append hprefix tailTrace_1550242
  have hstable : (prefixWord ++ tailWord_1550242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550242).length < 2 ^ (prefixWord ++ tailWord_1550242).sum := by decide
  have hdescent : baseEnd_1550242 < baseStart_1550242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
