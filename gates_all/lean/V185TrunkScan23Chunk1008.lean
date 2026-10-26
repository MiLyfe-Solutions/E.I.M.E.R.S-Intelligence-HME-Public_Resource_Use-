import V185TrunkScan23Chunk1007

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5968812 : List Nat := [2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 3]
def baseStart_5968812 : Nat := 118140960795 + 5968812 * 2 ^ 59
def prefixEnd_5968812 : Nat := 4983230072969 + 3 ^ 40 * 5968812 * 2
def baseEnd_5968812 : Nat := 3064869492324206229299939

theorem tailTrace_5968812 : CollatzResearch.WordTrace tailWord_5968812 prefixEnd_5968812 3064869492324206229299939 := by
  unfold tailWord_5968812
  simp only [CollatzResearch.WordTrace]
  refine ⟨108850229226010495388386345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145133638968013993851181793 108850229226010495388386345)
  ·
    refine ⟨81637671919507871541289759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108850229226010495388386345 81637671919507871541289759)
    ·
      refine ⟨122456507879261807311934639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81637671919507871541289759 122456507879261807311934639)
      ·
        refine ⟨183684761818892710967901959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122456507879261807311934639 183684761818892710967901959)
        ·
          refine ⟨275527142728339066451852939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183684761818892710967901959 275527142728339066451852939)
          ·
            refine ⟨413290714092508599677779409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275527142728339066451852939 413290714092508599677779409)
            ·
              refine ⟨309968035569381449758334557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 413290714092508599677779409 309968035569381449758334557)
              ·
                refine ⟨116238013338518043659375459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 309968035569381449758334557 116238013338518043659375459)
                ·
                  refine ⟨174357020007777065489063189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116238013338518043659375459 174357020007777065489063189)
                  ·
                    refine ⟨8172985312864549944799837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 174357020007777065489063189 8172985312864549944799837)
                    ·
                      refine ⟨3064869492324206229299939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8172985312864549944799837 3064869492324206229299939)
                      ·
                        rfl

theorem cell23_5968812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 3].length) (baseStart_5968812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5968812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5968812 prefixEnd_5968812 := by exact prefixLift 5968812
  have htrace : WordTrace (prefixWord ++ tailWord_5968812) baseStart_5968812 baseEnd_5968812 := by
    simpa [prefixWord, tailWord_5968812, baseEnd_5968812] using wordTrace_append hprefix tailTrace_5968812
  have hstable : (prefixWord ++ tailWord_5968812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5968812).length < 2 ^ (prefixWord ++ tailWord_5968812).sum := by decide
  have hdescent : baseEnd_5968812 < baseStart_5968812 := by decide
  rcases family_descends (prefixWord ++ tailWord_5968812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5968820 : List Nat := [2, 5, 2, 1, 1, 2, 1, 3, 2, 1, 3]
def baseStart_5968820 : Nat := 118140960795 + 5968820 * 2 ^ 59
def prefixEnd_5968820 : Nat := 4983230072969 + 3 ^ 40 * 5968820 * 2
def baseEnd_5968820 : Nat := 3064873600169442197999903

theorem tailTrace_5968820 : CollatzResearch.WordTrace tailWord_5968820 prefixEnd_5968820 3064873600169442197999903 := by
  unfold tailWord_5968820
  simp only [CollatzResearch.WordTrace]
  refine ⟨108850375117996004071531957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145133833490661338762042609 108850375117996004071531957)
  ·
    refine ⟨10204722667312125381706121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108850375117996004071531957 10204722667312125381706121)
    ·
      refine ⟨7653542000484094036279591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10204722667312125381706121 7653542000484094036279591)
      ·
        refine ⟨11480313000726141054419387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7653542000484094036279591 11480313000726141054419387)
        ·
          refine ⟨17220469501089211581629081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11480313000726141054419387 17220469501089211581629081)
          ·
            refine ⟨12915352125816908686221811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17220469501089211581629081 12915352125816908686221811)
            ·
              refine ⟨19373028188725363029332717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12915352125816908686221811 19373028188725363029332717)
              ·
                refine ⟨7264885570772011135999769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19373028188725363029332717 7264885570772011135999769)
                ·
                  refine ⟨5448664178079008351999827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7264885570772011135999769 5448664178079008351999827)
                  ·
                    refine ⟨8172996267118512527999741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5448664178079008351999827 8172996267118512527999741)
                    ·
                      refine ⟨3064873600169442197999903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8172996267118512527999741 3064873600169442197999903)
                      ·
                        rfl

theorem cell23_5968820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_5968820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5968820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5968820 prefixEnd_5968820 := by exact prefixLift 5968820
  have htrace : WordTrace (prefixWord ++ tailWord_5968820) baseStart_5968820 baseEnd_5968820 := by
    simpa [prefixWord, tailWord_5968820, baseEnd_5968820] using wordTrace_append hprefix tailTrace_5968820
  have hstable : (prefixWord ++ tailWord_5968820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5968820).length < 2 ^ (prefixWord ++ tailWord_5968820).sum := by decide
  have hdescent : baseEnd_5968820 < baseStart_5968820 := by decide
  rcases family_descends (prefixWord ++ tailWord_5968820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5968849 : List Nat := [1, 2, 2, 1, 2, 1, 4, 5, 5]
def baseStart_5968849 : Nat := 118140960795 + 5968849 * 2 ^ 59
def prefixEnd_5968849 : Nat := 4983230072969 + 3 ^ 40 * 5968849 * 2
def baseEnd_5968849 : Nat := 340543165678713620504141

theorem tailTrace_5968849 : CollatzResearch.WordTrace tailWord_5968849 prefixEnd_5968849 340543165678713620504141 := by
  unfold tailWord_5968849
  simp only [CollatzResearch.WordTrace]
  refine ⟨217701807952886946095869601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145134538635257964063913067 217701807952886946095869601)
  ·
    refine ⟨163276355964665209571902201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217701807952886946095869601 163276355964665209571902201)
    ·
      refine ⟨122457266973498907178926651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163276355964665209571902201 122457266973498907178926651)
      ·
        refine ⟨183685900460248360768389977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122457266973498907178926651 183685900460248360768389977)
        ·
          refine ⟨137764425345186270576292483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183685900460248360768389977 137764425345186270576292483)
          ·
            refine ⟨206646638017779405864438725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137764425345186270576292483 206646638017779405864438725)
            ·
              refine ⟨38746244628333638599582261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 206646638017779405864438725 38746244628333638599582261)
              ·
                refine ⟨3632460433906278618710837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38746244628333638599582261 3632460433906278618710837)
                ·
                  refine ⟨340543165678713620504141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3632460433906278618710837 340543165678713620504141)
                  ·
                    rfl

theorem cell23_5968849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 5, 5].length) (baseStart_5968849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5968849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5968849 prefixEnd_5968849 := by exact prefixLift 5968849
  have htrace : WordTrace (prefixWord ++ tailWord_5968849) baseStart_5968849 baseEnd_5968849 := by
    simpa [prefixWord, tailWord_5968849, baseEnd_5968849] using wordTrace_append hprefix tailTrace_5968849
  have hstable : (prefixWord ++ tailWord_5968849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5968849).length < 2 ^ (prefixWord ++ tailWord_5968849).sum := by decide
  have hdescent : baseEnd_5968849 < baseStart_5968849 := by decide
  rcases family_descends (prefixWord ++ tailWord_5968849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5968949 : List Nat := [1, 3, 3, 1, 1, 1, 1, 1, 1, 7, 3]
def baseStart_5968949 : Nat := 118140960795 + 5968949 * 2 ^ 59
def prefixEnd_5968949 : Nat := 4983230072969 + 3 ^ 40 * 5968949 * 2
def baseEnd_5968949 : Nat := 3064939839173872193286809

theorem tailTrace_5968949 : CollatzResearch.WordTrace tailWord_5968949 prefixEnd_5968949 3064939839173872193286809 := by
  unfold tailWord_5968949
  simp only [CollatzResearch.WordTrace]
  refine ⟨217705455252524663174509901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145136970168349775449673267 217705455252524663174509901)
  ·
    refine ⟨81639545719696748690441213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217705455252524663174509901 81639545719696748690441213)
    ·
      refine ⟨30614829644886280758915455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81639545719696748690441213 30614829644886280758915455)
      ·
        refine ⟨45922244467329421138373183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30614829644886280758915455 45922244467329421138373183)
        ·
          refine ⟨68883366700994131707559775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45922244467329421138373183 68883366700994131707559775)
          ·
            refine ⟨103325050051491197561339663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68883366700994131707559775 103325050051491197561339663)
            ·
              refine ⟨154987575077236796342009495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103325050051491197561339663 154987575077236796342009495)
              ·
                refine ⟨232481362615855194513014243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154987575077236796342009495 232481362615855194513014243)
                ·
                  refine ⟨348722043923782791769521365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 232481362615855194513014243 348722043923782791769521365)
                  ·
                    refine ⟨8173172904463659182098157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 348722043923782791769521365 8173172904463659182098157)
                    ·
                      refine ⟨3064939839173872193286809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8173172904463659182098157 3064939839173872193286809)
                      ·
                        rfl

theorem cell23_5968949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_5968949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5968949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5968949 prefixEnd_5968949 := by exact prefixLift 5968949
  have htrace : WordTrace (prefixWord ++ tailWord_5968949) baseStart_5968949 baseEnd_5968949 := by
    simpa [prefixWord, tailWord_5968949, baseEnd_5968949] using wordTrace_append hprefix tailTrace_5968949
  have hstable : (prefixWord ++ tailWord_5968949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5968949).length < 2 ^ (prefixWord ++ tailWord_5968949).sum := by decide
  have hdescent : baseEnd_5968949 < baseStart_5968949 := by decide
  rcases family_descends (prefixWord ++ tailWord_5968949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5968990 : List Nat := [4, 4, 1, 1, 1, 2, 1, 3, 6]
def baseStart_5968990 : Nat := 118140960795 + 5968990 * 2 ^ 59
def prefixEnd_5968990 : Nat := 4983230072969 + 3 ^ 40 * 5968990 * 2
def baseEnd_5968990 : Nat := 340551210208967392541569

theorem tailTrace_5968990 : CollatzResearch.WordTrace tailWord_5968990 prefixEnd_5968990 340551210208967392541569 := by
  unfold tailWord_5968990
  simp only [CollatzResearch.WordTrace]
  refine ⟨27213368830672015897094053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145137967096917418117834949 27213368830672015897094053)
  ·
    refine ⟨5102506655751002980705135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27213368830672015897094053 5102506655751002980705135)
    ·
      refine ⟨7653759983626504471057703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5102506655751002980705135 7653759983626504471057703)
      ·
        refine ⟨11480639975439756706586555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7653759983626504471057703 11480639975439756706586555)
        ·
          refine ⟨17220959963159635059879833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11480639975439756706586555 17220959963159635059879833)
          ·
            refine ⟨12915719972369726294909875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17220959963159635059879833 12915719972369726294909875)
            ·
              refine ⟨19373579958554589442364813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12915719972369726294909875 19373579958554589442364813)
              ·
                refine ⟨7265092484457971040886805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19373579958554589442364813 7265092484457971040886805)
                ·
                  refine ⟨340551210208967392541569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7265092484457971040886805 340551210208967392541569)
                  ·
                    rfl

theorem cell23_5968990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_5968990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5968990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5968990 prefixEnd_5968990 := by exact prefixLift 5968990
  have htrace : WordTrace (prefixWord ++ tailWord_5968990) baseStart_5968990 baseEnd_5968990 := by
    simpa [prefixWord, tailWord_5968990, baseEnd_5968990] using wordTrace_append hprefix tailTrace_5968990
  have hstable : (prefixWord ++ tailWord_5968990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5968990).length < 2 ^ (prefixWord ++ tailWord_5968990).sum := by decide
  have hdescent : baseEnd_5968990 < baseStart_5968990 := by decide
  rcases family_descends (prefixWord ++ tailWord_5968990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5969029 : List Nat := [1, 3, 1, 1, 6, 11]
def baseStart_5969029 : Nat := 118140960795 + 5969029 * 2 ^ 59
def prefixEnd_5969029 : Nat := 4983230072969 + 3 ^ 40 * 5969029 * 2
def baseEnd_5969029 : Nat := 12613090195992723787187

theorem tailTrace_5969029 : CollatzResearch.WordTrace tailWord_5969029 prefixEnd_5969029 12613090195992723787187 := by
  unfold tailWord_5969029
  simp only [CollatzResearch.WordTrace]
  refine ⟨217708373092234836837422141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145138915394823224558281427 217708373092234836837422141)
  ·
    refine ⟨81640639909588063814033303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217708373092234836837422141 81640639909588063814033303)
    ·
      refine ⟨122460959864382095721049955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81640639909588063814033303 122460959864382095721049955)
      ·
        refine ⟨183691439796573143581574933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122460959864382095721049955 183691439796573143581574933)
        ·
          refine ⟨8610536240464366105386325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 183691439796573143581574933 8610536240464366105386325)
          ·
            refine ⟨12613090195992723787187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8610536240464366105386325 12613090195992723787187)
            ·
              rfl

theorem cell23_5969029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 11].length) (baseStart_5969029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5969029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5969029 prefixEnd_5969029 := by exact prefixLift 5969029
  have htrace : WordTrace (prefixWord ++ tailWord_5969029) baseStart_5969029 baseEnd_5969029 := by
    simpa [prefixWord, tailWord_5969029, baseEnd_5969029] using wordTrace_append hprefix tailTrace_5969029
  have hstable : (prefixWord ++ tailWord_5969029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5969029).length < 2 ^ (prefixWord ++ tailWord_5969029).sum := by decide
  have hdescent : baseEnd_5969029 < baseStart_5969029 := by decide
  rcases family_descends (prefixWord ++ tailWord_5969029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5969033 : List Nat := [1, 2, 1, 1, 4, 4, 2, 2, 2, 4]
def baseStart_5969033 : Nat := 118140960795 + 5969033 * 2 ^ 59
def prefixEnd_5969033 : Nat := 4983230072969 + 3 ^ 40 * 5969033 * 2
def baseEnd_5969033 : Nat := 1021660990516283288212141

theorem tailTrace_5969033 : CollatzResearch.WordTrace tailWord_5969033 prefixEnd_5969033 1021660990516283288212141 := by
  unfold tailWord_5969033
  simp only [CollatzResearch.WordTrace]
  refine ⟨217708518984220345520567753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145139012656146897013711835 217708518984220345520567753)
  ·
    refine ⟨163281389238165259140425815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217708518984220345520567753 163281389238165259140425815)
    ·
      refine ⟨244922083857247888710638723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163281389238165259140425815 244922083857247888710638723)
      ·
        refine ⟨367383125785871833065958085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244922083857247888710638723 367383125785871833065958085)
        ·
          refine ⟨68884336084850968699867141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 367383125785871833065958085 68884336084850968699867141)
          ·
            refine ⟨12915813015909556631225089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68884336084850968699867141 12915813015909556631225089)
            ·
              refine ⟨9686859761932167473418817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12915813015909556631225089 9686859761932167473418817)
              ·
                refine ⟨7265144821449125605064113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9686859761932167473418817 7265144821449125605064113)
                ·
                  refine ⟨5448858616086844203798085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7265144821449125605064113 5448858616086844203798085)
                  ·
                    refine ⟨1021660990516283288212141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5448858616086844203798085 1021660990516283288212141)
                    ·
                      rfl

theorem cell23_5969033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 2, 2, 4].length) (baseStart_5969033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5969033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5969033 prefixEnd_5969033 := by exact prefixLift 5969033
  have htrace : WordTrace (prefixWord ++ tailWord_5969033) baseStart_5969033 baseEnd_5969033 := by
    simpa [prefixWord, tailWord_5969033, baseEnd_5969033] using wordTrace_append hprefix tailTrace_5969033
  have hstable : (prefixWord ++ tailWord_5969033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5969033).length < 2 ^ (prefixWord ++ tailWord_5969033).sum := by decide
  have hdescent : baseEnd_5969033 < baseStart_5969033 := by decide
  rcases family_descends (prefixWord ++ tailWord_5969033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5969063 : List Nat := [1, 1, 6, 2, 1, 2, 3, 7]
def baseStart_5969063 : Nat := 118140960795 + 5969063 * 2 ^ 59
def prefixEnd_5969063 : Nat := 4983230072969 + 3 ^ 40 * 5969063 * 2
def baseEnd_5969063 : Nat := 113518458369203138787455

theorem tailTrace_5969063 : CollatzResearch.WordTrace tailWord_5969063 prefixEnd_5969063 113518458369203138787455 := by
  unfold tailWord_5969063
  simp only [CollatzResearch.WordTrace]
  refine ⟨217709613174111660644159843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145139742116074440429439895 217709613174111660644159843)
  ·
    refine ⟨326564419761167490966239765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217709613174111660644159843 326564419761167490966239765)
    ·
      refine ⟨15307707176304726139042489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 326564419761167490966239765 15307707176304726139042489)
      ·
        refine ⟨11480780382228544604281867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15307707176304726139042489 11480780382228544604281867)
        ·
          refine ⟨17221170573342816906422801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11480780382228544604281867 17221170573342816906422801)
          ·
            refine ⟨12915877930007112679817101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17221170573342816906422801 12915877930007112679817101)
            ·
              refine ⟨4843454223752667254931413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12915877930007112679817101 4843454223752667254931413)
              ·
                refine ⟨113518458369203138787455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4843454223752667254931413 113518458369203138787455)
                ·
                  rfl

theorem cell23_5969063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3, 7].length) (baseStart_5969063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5969063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5969063 prefixEnd_5969063 := by exact prefixLift 5969063
  have htrace : WordTrace (prefixWord ++ tailWord_5969063) baseStart_5969063 baseEnd_5969063 := by
    simpa [prefixWord, tailWord_5969063, baseEnd_5969063] using wordTrace_append hprefix tailTrace_5969063
  have hstable : (prefixWord ++ tailWord_5969063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5969063).length < 2 ^ (prefixWord ++ tailWord_5969063).sum := by decide
  have hdescent : baseEnd_5969063 < baseStart_5969063 := by decide
  rcases family_descends (prefixWord ++ tailWord_5969063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5969073 : List Nat := [1, 2, 2, 5, 1, 1, 2, 2, 1, 3, 3]
def baseStart_5969073 : Nat := 118140960795 + 5969073 * 2 ^ 59
def prefixEnd_5969073 : Nat := 4983230072969 + 3 ^ 40 * 5969073 * 2
def baseEnd_5969073 : Nat := 3065003510775029708136239

theorem tailTrace_5969073 : CollatzResearch.WordTrace tailWord_5969073 prefixEnd_5969073 3065003510775029708136239 := by
  unfold tailWord_5969073
  simp only [CollatzResearch.WordTrace]
  refine ⟨217709977904075432352023873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145139985269383621568015915 217709977904075432352023873)
  ·
    refine ⟨163282483428056574264017905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217709977904075432352023873 163282483428056574264017905)
    ·
      refine ⟨122461862571042430698013429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163282483428056574264017905 122461862571042430698013429)
      ·
        refine ⟨11480799616035227877938759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 122461862571042430698013429 11480799616035227877938759)
        ·
          refine ⟨17221199424052841816908139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11480799616035227877938759 17221199424052841816908139)
          ·
            refine ⟨25831799136079262725362209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17221199424052841816908139 25831799136079262725362209)
            ·
              refine ⟨19373849352059447044021657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25831799136079262725362209 19373849352059447044021657)
              ·
                refine ⟨14530387014044585283016243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19373849352059447044021657 14530387014044585283016243)
                ·
                  refine ⟨21795580521066877924524365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14530387014044585283016243 21795580521066877924524365)
                  ·
                    refine ⟨8173342695400079221696637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21795580521066877924524365 8173342695400079221696637)
                    ·
                      refine ⟨3065003510775029708136239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8173342695400079221696637 3065003510775029708136239)
                      ·
                        rfl

theorem cell23_5969073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_5969073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5969073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5969073 prefixEnd_5969073 := by exact prefixLift 5969073
  have htrace : WordTrace (prefixWord ++ tailWord_5969073) baseStart_5969073 baseEnd_5969073 := by
    simpa [prefixWord, tailWord_5969073, baseEnd_5969073] using wordTrace_append hprefix tailTrace_5969073
  have hstable : (prefixWord ++ tailWord_5969073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5969073).length < 2 ^ (prefixWord ++ tailWord_5969073).sum := by decide
  have hdescent : baseEnd_5969073 < baseStart_5969073 := by decide
  rcases family_descends (prefixWord ++ tailWord_5969073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5969099 : List Nat := [1, 1, 1, 1, 3, 2, 2, 1, 3, 3, 5]
def baseStart_5969099 : Nat := 118140960795 + 5969099 * 2 ^ 59
def prefixEnd_5969099 : Nat := 4983230072969 + 3 ^ 40 * 5969099 * 2
def baseEnd_5969099 : Nat := 3065016861272046606411119

theorem tailTrace_5969099 : CollatzResearch.WordTrace tailWord_5969099 prefixEnd_5969099 3065016861272046606411119 := by
  unfold tailWord_5969099
  simp only [CollatzResearch.WordTrace]
  refine ⟨217710926201981238792470351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145140617467987492528313567 217710926201981238792470351)
  ·
    refine ⟨326566389302971858188705527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217710926201981238792470351 326566389302971858188705527)
    ·
      refine ⟨489849583954457787283058291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326566389302971858188705527 489849583954457787283058291)
      ·
        refine ⟨734774375931686680924587437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 489849583954457787283058291 734774375931686680924587437)
        ·
          refine ⟨275540390974382505346720289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 734774375931686680924587437 275540390974382505346720289)
          ·
            refine ⟨206655293230786879010040217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 275540390974382505346720289 206655293230786879010040217)
            ·
              refine ⟨154991469923090159257530163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 206655293230786879010040217 154991469923090159257530163)
              ·
                refine ⟨232487204884635238886295245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154991469923090159257530163 232487204884635238886295245)
                ·
                  refine ⟨87182701831738214582360717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 232487204884635238886295245 87182701831738214582360717)
                  ·
                    refine ⟨32693513186901830468385269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 87182701831738214582360717 32693513186901830468385269)
                    ·
                      refine ⟨3065016861272046606411119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32693513186901830468385269 3065016861272046606411119)
                      ·
                        rfl

theorem cell23_5969099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3, 5].length) (baseStart_5969099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5969099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5969099 prefixEnd_5969099 := by exact prefixLift 5969099
  have htrace : WordTrace (prefixWord ++ tailWord_5969099) baseStart_5969099 baseEnd_5969099 := by
    simpa [prefixWord, tailWord_5969099, baseEnd_5969099] using wordTrace_append hprefix tailTrace_5969099
  have hstable : (prefixWord ++ tailWord_5969099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5969099).length < 2 ^ (prefixWord ++ tailWord_5969099).sum := by decide
  have hdescent : baseEnd_5969099 < baseStart_5969099 := by decide
  rcases family_descends (prefixWord ++ tailWord_5969099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5969106 : List Nat := [3, 2, 2, 2, 1, 1, 1, 3, 2, 6]
def baseStart_5969106 : Nat := 118140960795 + 5969106 * 2 ^ 59
def prefixEnd_5969106 : Nat := 4983230072969 + 3 ^ 40 * 5969106 * 2
def baseEnd_5969106 : Nat := 1021673485212209359674529

theorem tailTrace_5969106 : CollatzResearch.WordTrace tailWord_5969106 prefixEnd_5969106 1021673485212209359674529 := by
  unfold tailWord_5969106
  simp only [CollatzResearch.WordTrace]
  refine ⟨54427795378238969746993793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145140787675303919325316781 54427795378238969746993793)
  ·
    refine ⟨40820846533679227310245345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54427795378238969746993793 40820846533679227310245345)
    ·
      refine ⟨30615634900259420482684009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40820846533679227310245345 30615634900259420482684009)
      ·
        refine ⟨22961726175194565362013007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30615634900259420482684009 22961726175194565362013007)
        ·
          refine ⟨34442589262791848043019511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22961726175194565362013007 34442589262791848043019511)
          ·
            refine ⟨51663883894187772064529267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34442589262791848043019511 51663883894187772064529267)
            ·
              refine ⟨77495825841281658096793901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51663883894187772064529267 77495825841281658096793901)
              ·
                refine ⟨29060934690480621786297713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77495825841281658096793901 29060934690480621786297713)
                ·
                  refine ⟨21795701017860466339723285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29060934690480621786297713 21795701017860466339723285)
                  ·
                    refine ⟨1021673485212209359674529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21795701017860466339723285 1021673485212209359674529)
                    ·
                      rfl

theorem cell23_5969106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_5969106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5969106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5969106 prefixEnd_5969106 := by exact prefixLift 5969106
  have htrace : WordTrace (prefixWord ++ tailWord_5969106) baseStart_5969106 baseEnd_5969106 := by
    simpa [prefixWord, tailWord_5969106, baseEnd_5969106] using wordTrace_append hprefix tailTrace_5969106
  have hstable : (prefixWord ++ tailWord_5969106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5969106).length < 2 ^ (prefixWord ++ tailWord_5969106).sum := by decide
  have hdescent : baseEnd_5969106 < baseStart_5969106 := by decide
  rcases family_descends (prefixWord ++ tailWord_5969106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5969129 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 3, 2, 7]
def baseStart_5969129 : Nat := 118140960795 + 5969129 * 2 ^ 59
def prefixEnd_5969129 : Nat := 4983230072969 + 3 ^ 40 * 5969129 * 2
def baseEnd_5969129 : Nat := 3065032265691681489035981

theorem tailTrace_5969129 : CollatzResearch.WordTrace tailWord_5969129 prefixEnd_5969129 3065032265691681489035981 := by
  unfold tailWord_5969129
  simp only [CollatzResearch.WordTrace]
  refine ⟨217712020391872553916062441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145141346927915035944041627 217712020391872553916062441)
  ·
    refine ⟨163284015293904415437046831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217712020391872553916062441 163284015293904415437046831)
    ·
      refine ⟨244926022940856623155570247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163284015293904415437046831 244926022940856623155570247)
      ·
        refine ⟨367389034411284934733355371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244926022940856623155570247 367389034411284934733355371)
        ·
          refine ⟨551083551616927402100033057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367389034411284934733355371 551083551616927402100033057)
          ·
            refine ⟨413312663712695551575024793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 551083551616927402100033057 413312663712695551575024793)
            ·
              refine ⟨309984497784521663681268595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 413312663712695551575024793 309984497784521663681268595)
              ·
                refine ⟨464976746676782495521902893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 309984497784521663681268595 464976746676782495521902893)
                ·
                  refine ⟨174366280003793435820713585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 464976746676782495521902893 174366280003793435820713585)
                  ·
                    refine ⟨130774710002845076865535189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 174366280003793435820713585 130774710002845076865535189)
                    ·
                      refine ⟨3065032265691681489035981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 130774710002845076865535189 3065032265691681489035981)
                      ·
                        rfl

theorem cell23_5969129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 2, 7].length) (baseStart_5969129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5969129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5969129 prefixEnd_5969129 := by exact prefixLift 5969129
  have htrace : WordTrace (prefixWord ++ tailWord_5969129) baseStart_5969129 baseEnd_5969129 := by
    simpa [prefixWord, tailWord_5969129, baseEnd_5969129] using wordTrace_append hprefix tailTrace_5969129
  have hstable : (prefixWord ++ tailWord_5969129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5969129).length < 2 ^ (prefixWord ++ tailWord_5969129).sum := by decide
  have hdescent : baseEnd_5969129 < baseStart_5969129 := by decide
  rcases family_descends (prefixWord ++ tailWord_5969129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5969130 : List Nat := [3, 1, 3, 1, 1, 3, 1, 2, 4, 2, 2]
def baseStart_5969130 : Nat := 118140960795 + 5969130 * 2 ^ 59
def prefixEnd_5969130 : Nat := 4983230072969 + 3 ^ 40 * 5969130 * 2
def baseEnd_5969130 : Nat := 3065032779172335985123477

theorem tailTrace_5969130 : CollatzResearch.WordTrace tailWord_5969130 prefixEnd_5969130 3065032779172335985123477 := by
  unfold tailWord_5969130
  simp only [CollatzResearch.WordTrace]
  refine ⟨54428014216217232771712211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145141371243245954057899229 54428014216217232771712211)
  ·
    refine ⟨81642021324325849157568317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54428014216217232771712211 81642021324325849157568317)
    ·
      refine ⟨30615757996622193434088119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81642021324325849157568317 30615757996622193434088119)
      ·
        refine ⟨45923636994933290151132179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30615757996622193434088119 45923636994933290151132179)
        ·
          refine ⟨68885455492399935226698269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45923636994933290151132179 68885455492399935226698269)
          ·
            refine ⟨25832045809649975710011851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68885455492399935226698269 25832045809649975710011851)
            ·
              refine ⟨38748068714474963565017777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25832045809649975710011851 38748068714474963565017777)
              ·
                refine ⟨29061051535856222673763333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38748068714474963565017777 29061051535856222673763333)
                ·
                  refine ⟨5448947162973041751330625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29061051535856222673763333 5448947162973041751330625)
                  ·
                    refine ⟨4086710372229781313497969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5448947162973041751330625 4086710372229781313497969)
                    ·
                      refine ⟨3065032779172335985123477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4086710372229781313497969 3065032779172335985123477)
                      ·
                        rfl

theorem cell23_5969130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 4, 2, 2].length) (baseStart_5969130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5969130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5969130 prefixEnd_5969130 := by exact prefixLift 5969130
  have htrace : WordTrace (prefixWord ++ tailWord_5969130) baseStart_5969130 baseEnd_5969130 := by
    simpa [prefixWord, tailWord_5969130, baseEnd_5969130] using wordTrace_append hprefix tailTrace_5969130
  have hstable : (prefixWord ++ tailWord_5969130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5969130).length < 2 ^ (prefixWord ++ tailWord_5969130).sum := by decide
  have hdescent : baseEnd_5969130 < baseStart_5969130 := by decide
  rcases family_descends (prefixWord ++ tailWord_5969130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5969133 : List Nat := [1, 5, 1, 2, 2, 2, 1, 1, 2, 1, 5]
def baseStart_5969133 : Nat := 118140960795 + 5969133 * 2 ^ 59
def prefixEnd_5969133 : Nat := 4983230072969 + 3 ^ 40 * 5969133 * 2
def baseEnd_5969133 : Nat := 3065034319614299473385963

theorem tailTrace_5969133 : CollatzResearch.WordTrace tailWord_5969133 prefixEnd_5969133 3065034319614299473385963 := by
  unfold tailWord_5969133
  simp only [CollatzResearch.WordTrace]
  refine ⟨217712166283858062599208053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145141444189238708399472035 217712166283858062599208053)
  ·
    refine ⟨20410515589111693368675755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 217712166283858062599208053 20410515589111693368675755)
    ·
      refine ⟨30615773383667540053013633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20410515589111693368675755 30615773383667540053013633)
      ·
        refine ⟨22961830037750655039760225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30615773383667540053013633 22961830037750655039760225)
        ·
          refine ⟨17221372528312991279820169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22961830037750655039760225 17221372528312991279820169)
          ·
            refine ⟨12916029396234743459865127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17221372528312991279820169 12916029396234743459865127)
            ·
              refine ⟨19374044094352115189797691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12916029396234743459865127 19374044094352115189797691)
              ·
                refine ⟨29061066141528172784696537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19374044094352115189797691 29061066141528172784696537)
                ·
                  refine ⟨21795799606146129588522403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29061066141528172784696537 21795799606146129588522403)
                  ·
                    refine ⟨32693699409219194382783605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21795799606146129588522403 32693699409219194382783605)
                    ·
                      refine ⟨3065034319614299473385963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32693699409219194382783605 3065034319614299473385963)
                      ·
                        rfl

theorem cell23_5969133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_5969133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5969133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5969133 prefixEnd_5969133 := by exact prefixLift 5969133
  have htrace : WordTrace (prefixWord ++ tailWord_5969133) baseStart_5969133 baseEnd_5969133 := by
    simpa [prefixWord, tailWord_5969133, baseEnd_5969133] using wordTrace_append hprefix tailTrace_5969133
  have hstable : (prefixWord ++ tailWord_5969133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5969133).length < 2 ^ (prefixWord ++ tailWord_5969133).sum := by decide
  have hdescent : baseEnd_5969133 < baseStart_5969133 := by decide
  rcases family_descends (prefixWord ++ tailWord_5969133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5969153 : List Nat := [1, 2, 4, 1, 1, 5, 1, 1, 7]
def baseStart_5969153 : Nat := 118140960795 + 5969153 * 2 ^ 59
def prefixEnd_5969153 : Nat := 4983230072969 + 3 ^ 40 * 5969153 * 2
def baseEnd_5969153 : Nat := 340560509914154377237319

theorem tailTrace_5969153 : CollatzResearch.WordTrace tailWord_5969153 prefixEnd_5969153 340560509914154377237319 := by
  unfold tailWord_5969153
  simp only [CollatzResearch.WordTrace]
  refine ⟨217712895743785606014936113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145141930495857070676624075 217712895743785606014936113)
  ·
    refine ⟨163284671807839204511202085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217712895743785606014936113 163284671807839204511202085)
    ·
      refine ⟨30615875963969850845850391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163284671807839204511202085 30615875963969850845850391)
      ·
        refine ⟨45923813945954776268775587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30615875963969850845850391 45923813945954776268775587)
        ·
          refine ⟨68885720918932164403163381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45923813945954776268775587 68885720918932164403163381)
          ·
            refine ⟨6458036336149890412796567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68885720918932164403163381 6458036336149890412796567)
            ·
              refine ⟨9687054504224835619194851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6458036336149890412796567 9687054504224835619194851)
              ·
                refine ⟨14530581756337253428792277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9687054504224835619194851 14530581756337253428792277)
                ·
                  refine ⟨340560509914154377237319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14530581756337253428792277 340560509914154377237319)
                  ·
                    rfl

theorem cell23_5969153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 1, 7].length) (baseStart_5969153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5969153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5969153 prefixEnd_5969153 := by exact prefixLift 5969153
  have htrace : WordTrace (prefixWord ++ tailWord_5969153) baseStart_5969153 baseEnd_5969153 := by
    simpa [prefixWord, tailWord_5969153, baseEnd_5969153] using wordTrace_append hprefix tailTrace_5969153
  have hstable : (prefixWord ++ tailWord_5969153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5969153).length < 2 ^ (prefixWord ++ tailWord_5969153).sum := by decide
  have hdescent : baseEnd_5969153 < baseStart_5969153 := by decide
  rcases family_descends (prefixWord ++ tailWord_5969153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5969164 : List Nat := [2, 2, 1, 2, 2, 5, 2, 1, 2, 2, 2]
def baseStart_5969164 : Nat := 118140960795 + 5969164 * 2 ^ 59
def prefixEnd_5969164 : Nat := 4983230072969 + 3 ^ 40 * 5969164 * 2
def baseEnd_5969164 : Nat := 3065050237514588852098321

theorem tailTrace_5969164 : CollatzResearch.WordTrace tailWord_5969164 prefixEnd_5969164 3065050237514588852098321 := by
  unfold tailWord_5969164
  simp only [CollatzResearch.WordTrace]
  refine ⟨108856648473372877446793273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145142197964497169929057697 108856648473372877446793273)
  ·
    refine ⟨81642486355029658085094955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108856648473372877446793273 81642486355029658085094955)
    ·
      refine ⟨122463729532544487127642433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81642486355029658085094955 122463729532544487127642433)
      ·
        refine ⟨91847797149408365345731825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122463729532544487127642433 91847797149408365345731825)
        ·
          refine ⟨68885847862056274009298869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91847797149408365345731825 68885847862056274009298869)
          ·
            refine ⟨6458048237067775688371769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68885847862056274009298869 6458048237067775688371769)
            ·
              refine ⟨4843536177800831766278827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6458048237067775688371769 4843536177800831766278827)
              ·
                refine ⟨7265304266701247649418241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4843536177800831766278827 7265304266701247649418241)
                ·
                  refine ⟨5448978200025935737063681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7265304266701247649418241 5448978200025935737063681)
                  ·
                    refine ⟨4086733650019451802797761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5448978200025935737063681 4086733650019451802797761)
                    ·
                      refine ⟨3065050237514588852098321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4086733650019451802797761 3065050237514588852098321)
                      ·
                        rfl

theorem cell23_5969164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2, 1, 2, 2, 2].length) (baseStart_5969164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5969164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5969164 prefixEnd_5969164 := by exact prefixLift 5969164
  have htrace : WordTrace (prefixWord ++ tailWord_5969164) baseStart_5969164 baseEnd_5969164 := by
    simpa [prefixWord, tailWord_5969164, baseEnd_5969164] using wordTrace_append hprefix tailTrace_5969164
  have hstable : (prefixWord ++ tailWord_5969164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5969164).length < 2 ^ (prefixWord ++ tailWord_5969164).sum := by decide
  have hdescent : baseEnd_5969164 < baseStart_5969164 := by decide
  rcases family_descends (prefixWord ++ tailWord_5969164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5969203 : List Nat := [1, 1, 1, 2, 5, 2, 2, 2, 2, 1, 4]
def baseStart_5969203 : Nat := 118140960795 + 5969203 * 2 ^ 59
def prefixEnd_5969203 : Nat := 4983230072969 + 3 ^ 40 * 5969203 * 2
def baseEnd_5969203 : Nat := 3065070263260114199510641

theorem tailTrace_5969203 : CollatzResearch.WordTrace tailWord_5969203 prefixEnd_5969203 3065070263260114199510641 := by
  unfold tailWord_5969203
  simp only [CollatzResearch.WordTrace]
  refine ⟨217714719393604464554256263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145143146262402976369504175 217714719393604464554256263)
  ·
    refine ⟨326572079090406696831384395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217714719393604464554256263 326572079090406696831384395)
    ·
      refine ⟨489858118635610045247076593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326572079090406696831384395 489858118635610045247076593)
      ·
        refine ⟨367393588976707533935307445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 489858118635610045247076593 367393588976707533935307445)
        ·
          refine ⟨34443148966566331306435073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 367393588976707533935307445 34443148966566331306435073)
          ·
            refine ⟨25832361724924748479826305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34443148966566331306435073 25832361724924748479826305)
            ·
              refine ⟨19374271293693561359869729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25832361724924748479826305 19374271293693561359869729)
              ·
                refine ⟨14530703470270171019902297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19374271293693561359869729 14530703470270171019902297)
                ·
                  refine ⟨10898027602702628264926723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14530703470270171019902297 10898027602702628264926723)
                  ·
                    refine ⟨16347041404053942397390085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10898027602702628264926723 16347041404053942397390085)
                    ·
                      refine ⟨3065070263260114199510641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16347041404053942397390085 3065070263260114199510641)
                      ·
                        rfl

theorem cell23_5969203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2, 2, 1, 4].length) (baseStart_5969203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5969203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5969203 prefixEnd_5969203 := by exact prefixLift 5969203
  have htrace : WordTrace (prefixWord ++ tailWord_5969203) baseStart_5969203 baseEnd_5969203 := by
    simpa [prefixWord, tailWord_5969203, baseEnd_5969203] using wordTrace_append hprefix tailTrace_5969203
  have hstable : (prefixWord ++ tailWord_5969203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5969203).length < 2 ^ (prefixWord ++ tailWord_5969203).sum := by decide
  have hdescent : baseEnd_5969203 < baseStart_5969203 := by decide
  rcases family_descends (prefixWord ++ tailWord_5969203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5969260 : List Nat := [2, 2, 1, 1, 5, 3, 1, 2, 6]
def baseStart_5969260 : Nat := 118140960795 + 5969260 * 2 ^ 59
def prefixEnd_5969260 : Nat := 4983230072969 + 3 ^ 40 * 5969260 * 2
def baseEnd_5969260 : Nat := 340566614628602275166431

theorem tailTrace_5969260 : CollatzResearch.WordTrace tailWord_5969260 prefixEnd_5969260 340566614628602275166431 := by
  unfold tailWord_5969260
  simp only [CollatzResearch.WordTrace]
  refine ⟨108858399177198981644540617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145144532236265308859387489 108858399177198981644540617)
  ·
    refine ⟨81643799382899236233405463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108858399177198981644540617 81643799382899236233405463)
    ·
      refine ⟨122465699074348854350108195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81643799382899236233405463 122465699074348854350108195)
      ·
        refine ⟨183698548611523281525162293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122465699074348854350108195 183698548611523281525162293)
        ·
          refine ⟨17221738932330307642983965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 183698548611523281525162293 17221738932330307642983965)
          ·
            refine ⟨6458152099623865366118987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17221738932330307642983965 6458152099623865366118987)
            ·
              refine ⟨9687228149435798049178481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6458152099623865366118987 9687228149435798049178481)
              ·
                refine ⟨7265421112076848536883861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9687228149435798049178481 7265421112076848536883861)
                ·
                  refine ⟨340566614628602275166431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7265421112076848536883861 340566614628602275166431)
                  ·
                    rfl

theorem cell23_5969260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 6].length) (baseStart_5969260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5969260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5969260 prefixEnd_5969260 := by exact prefixLift 5969260
  have htrace : WordTrace (prefixWord ++ tailWord_5969260) baseStart_5969260 baseEnd_5969260 := by
    simpa [prefixWord, tailWord_5969260, baseEnd_5969260] using wordTrace_append hprefix tailTrace_5969260
  have hstable : (prefixWord ++ tailWord_5969260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5969260).length < 2 ^ (prefixWord ++ tailWord_5969260).sum := by decide
  have hdescent : baseEnd_5969260 < baseStart_5969260 := by decide
  rcases family_descends (prefixWord ++ tailWord_5969260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5969296 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 5]
def baseStart_5969296 : Nat := 118140960795 + 5969296 * 2 ^ 59
def prefixEnd_5969296 : Nat := 4983230072969 + 3 ^ 40 * 5969296 * 2
def baseEnd_5969296 : Nat := 3065118016960982335647713

theorem tailTrace_5969296 : CollatzResearch.WordTrace tailWord_5969296 prefixEnd_5969296 3065118016960982335647713 := by
  unfold tailWord_5969296
  simp only [CollatzResearch.WordTrace]
  refine ⟨108859055691133770718695871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145145407588178360958261161 108859055691133770718695871)
  ·
    refine ⟨163288583536700656078043807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108859055691133770718695871 163288583536700656078043807)
    ·
      refine ⟨244932875305050984117065711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163288583536700656078043807 244932875305050984117065711)
      ·
        refine ⟨367399312957576476175598567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244932875305050984117065711 367399312957576476175598567)
        ·
          refine ⟨551098969436364714263397851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367399312957576476175598567 551098969436364714263397851)
          ·
            refine ⟨826648454154547071395096777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 551098969436364714263397851 826648454154547071395096777)
            ·
              refine ⟨619986340615910303546322583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 826648454154547071395096777 619986340615910303546322583)
              ·
                refine ⟨929979510923865455319483875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 619986340615910303546322583 929979510923865455319483875)
                ·
                  refine ⟨1394969266385798182979225813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 929979510923865455319483875 1394969266385798182979225813)
                  ·
                    refine ⟨32694592180917144913575605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1394969266385798182979225813 32694592180917144913575605)
                    ·
                      refine ⟨3065118016960982335647713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32694592180917144913575605 3065118016960982335647713)
                      ·
                        rfl

theorem cell23_5969296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 5].length) (baseStart_5969296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5969296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5969296 prefixEnd_5969296 := by exact prefixLift 5969296
  have htrace : WordTrace (prefixWord ++ tailWord_5969296) baseStart_5969296 baseEnd_5969296 := by
    simpa [prefixWord, tailWord_5969296, baseEnd_5969296] using wordTrace_append hprefix tailTrace_5969296
  have hstable : (prefixWord ++ tailWord_5969296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5969296).length < 2 ^ (prefixWord ++ tailWord_5969296).sum := by decide
  have hdescent : baseEnd_5969296 < baseStart_5969296 := by decide
  rcases family_descends (prefixWord ++ tailWord_5969296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5969298 : List Nat := [3, 2, 3, 3, 2, 1, 1, 3, 1, 4]
def baseStart_5969298 : Nat := 118140960795 + 5969298 * 2 ^ 59
def prefixEnd_5969298 : Nat := 4983230072969 + 3 ^ 40 * 5969298 * 2
def baseEnd_5969298 : Nat := 1021706347974097109274235

theorem tailTrace_5969298 : CollatzResearch.WordTrace tailWord_5969298 prefixEnd_5969298 1021706347974097109274235 := by
  unfold tailWord_5969298
  simp only [CollatzResearch.WordTrace]
  refine ⟨54429546082065073944741137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145145456218840197185976365 54429546082065073944741137)
  ·
    refine ⟨40822159561548805458555853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54429546082065073944741137 40822159561548805458555853)
    ·
      refine ⟨15308309835580802046958445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40822159561548805458555853 15308309835580802046958445)
      ·
        refine ⟨5740616188342800767609417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15308309835580802046958445 5740616188342800767609417)
        ·
          refine ⟨4305462141257100575707063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5740616188342800767609417 4305462141257100575707063)
          ·
            refine ⟨6458193211885650863560595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4305462141257100575707063 6458193211885650863560595)
            ·
              refine ⟨9687289817828476295340893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6458193211885650863560595 9687289817828476295340893)
              ·
                refine ⟨3632733681685678610752835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9687289817828476295340893 3632733681685678610752835)
                ·
                  refine ⟨5449100522528517916129253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3632733681685678610752835 5449100522528517916129253)
                  ·
                    refine ⟨1021706347974097109274235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5449100522528517916129253 1021706347974097109274235)
                    ·
                      rfl

theorem cell23_5969298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_5969298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5969298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5969298 prefixEnd_5969298 := by exact prefixLift 5969298
  have htrace : WordTrace (prefixWord ++ tailWord_5969298) baseStart_5969298 baseEnd_5969298 := by
    simpa [prefixWord, tailWord_5969298, baseEnd_5969298] using wordTrace_append hprefix tailTrace_5969298
  have hstable : (prefixWord ++ tailWord_5969298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5969298).length < 2 ^ (prefixWord ++ tailWord_5969298).sum := by decide
  have hdescent : baseEnd_5969298 < baseStart_5969298 := by decide
  rcases family_descends (prefixWord ++ tailWord_5969298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5969333 : List Nat := [1, 3, 3, 2, 2, 1, 1, 10]
def baseStart_5969333 : Nat := 118140960795 + 5969333 * 2 ^ 59
def prefixEnd_5969333 : Nat := 4983230072969 + 3 ^ 40 * 5969333 * 2
def baseEnd_5969333 : Nat := 113523593175748099662409

theorem tailTrace_5969333 : CollatzResearch.WordTrace tailWord_5969333 prefixEnd_5969333 113523593175748099662409 := by
  unfold tailWord_5969333
  simp only [CollatzResearch.WordTrace]
  refine ⟨217719460883133496756488653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145146307255422331170992435 217719460883133496756488653)
  ·
    refine ⟨81644797831175061283683245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217719460883133496756488653 81644797831175061283683245)
    ·
      refine ⟨30616799186690647981381217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81644797831175061283683245 30616799186690647981381217)
      ·
        refine ⟨22962599390017985986035913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30616799186690647981381217 22962599390017985986035913)
        ·
          refine ⟨17221949542513489489526935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22962599390017985986035913 17221949542513489489526935)
          ·
            refine ⟨25832924313770234234290403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17221949542513489489526935 25832924313770234234290403)
            ·
              refine ⟨38749386470655351351435605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25832924313770234234290403 38749386470655351351435605)
              ·
                refine ⟨113523593175748099662409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 38749386470655351351435605 113523593175748099662409)
                ·
                  rfl

theorem cell23_5969333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 10].length) (baseStart_5969333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5969333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5969333 prefixEnd_5969333 := by exact prefixLift 5969333
  have htrace : WordTrace (prefixWord ++ tailWord_5969333) baseStart_5969333 baseEnd_5969333 := by
    simpa [prefixWord, tailWord_5969333, baseEnd_5969333] using wordTrace_append hprefix tailTrace_5969333
  have hstable : (prefixWord ++ tailWord_5969333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5969333).length < 2 ^ (prefixWord ++ tailWord_5969333).sum := by decide
  have hdescent : baseEnd_5969333 < baseStart_5969333 := by decide
  rcases family_descends (prefixWord ++ tailWord_5969333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5969337 : List Nat := [1, 2, 1, 4, 4, 1, 1, 3, 2, 4]
def baseStart_5969337 : Nat := 118140960795 + 5969337 * 2 ^ 59
def prefixEnd_5969337 : Nat := 4983230072969 + 3 ^ 40 * 5969337 * 2
def baseEnd_5969337 : Nat := 1021713023222605558411675

theorem tailTrace_5969337 : CollatzResearch.WordTrace tailWord_5969337 prefixEnd_5969337 1021713023222605558411675 := by
  unfold tailWord_5969337
  simp only [CollatzResearch.WordTrace]
  refine ⟨217719606775119005439634265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145146404516746003626422843 217719606775119005439634265)
  ·
    refine ⟨163289705081339254079725699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217719606775119005439634265 163289705081339254079725699)
    ·
      refine ⟨244934557622008881119588549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163289705081339254079725699 244934557622008881119588549)
      ·
        refine ⟨45925229554126665209922853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 244934557622008881119588549 45925229554126665209922853)
        ·
          refine ⟨8610980541398749726860535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45925229554126665209922853 8610980541398749726860535)
          ·
            refine ⟨12916470812098124590290803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8610980541398749726860535 12916470812098124590290803)
            ·
              refine ⟨19374706218147186885436205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12916470812098124590290803 19374706218147186885436205)
              ·
                refine ⟨7265514831805195082038577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19374706218147186885436205 7265514831805195082038577)
                ·
                  refine ⟨5449136123853896311528933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7265514831805195082038577 5449136123853896311528933)
                  ·
                    refine ⟨1021713023222605558411675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5449136123853896311528933 1021713023222605558411675)
                    ·
                      rfl

theorem cell23_5969337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 3, 2, 4].length) (baseStart_5969337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5969337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5969337 prefixEnd_5969337 := by exact prefixLift 5969337
  have htrace : WordTrace (prefixWord ++ tailWord_5969337) baseStart_5969337 baseEnd_5969337 := by
    simpa [prefixWord, tailWord_5969337, baseEnd_5969337] using wordTrace_append hprefix tailTrace_5969337
  have hstable : (prefixWord ++ tailWord_5969337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5969337).length < 2 ^ (prefixWord ++ tailWord_5969337).sum := by decide
  have hdescent : baseEnd_5969337 < baseStart_5969337 := by decide
  rcases family_descends (prefixWord ++ tailWord_5969337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5969343 : List Nat := [1, 1, 2, 2, 2, 1, 1, 2, 5, 3, 3]
def baseStart_5969343 : Nat := 118140960795 + 5969343 * 2 ^ 59
def prefixEnd_5969343 : Nat := 4983230072969 + 3 ^ 40 * 5969343 * 2
def baseEnd_5969343 : Nat := 3065142150551743651759997

theorem tailTrace_5969343 : CollatzResearch.WordTrace tailWord_5969343 prefixEnd_5969343 3065142150551743651759997 := by
  unfold tailWord_5969343
  simp only [CollatzResearch.WordTrace]
  refine ⟨217719825613097268464352683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145146550408731512309568455 217719825613097268464352683)
  ·
    refine ⟨326579738419645902696529025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217719825613097268464352683 326579738419645902696529025)
    ·
      refine ⟨244934803814734427022396769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326579738419645902696529025 244934803814734427022396769)
      ·
        refine ⟨183701102861050820266797577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244934803814734427022396769 183701102861050820266797577)
        ·
          refine ⟨137775827145788115200098183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183701102861050820266797577 137775827145788115200098183)
          ·
            refine ⟨206663740718682172800147275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137775827145788115200098183 206663740718682172800147275)
            ·
              refine ⟨309995611078023259200220913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206663740718682172800147275 309995611078023259200220913)
              ·
                refine ⟨232496708308517444400165685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 309995611078023259200220913 232496708308517444400165685)
                ·
                  refine ⟨21796566403923510412515533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 232496708308517444400165685 21796566403923510412515533)
                  ·
                    refine ⟨8173712401471316404693325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21796566403923510412515533 8173712401471316404693325)
                    ·
                      refine ⟨3065142150551743651759997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8173712401471316404693325 3065142150551743651759997)
                      ·
                        rfl

theorem cell23_5969343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5, 3, 3].length) (baseStart_5969343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5969343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5969343 prefixEnd_5969343 := by exact prefixLift 5969343
  have htrace : WordTrace (prefixWord ++ tailWord_5969343) baseStart_5969343 baseEnd_5969343 := by
    simpa [prefixWord, tailWord_5969343, baseEnd_5969343] using wordTrace_append hprefix tailTrace_5969343
  have hstable : (prefixWord ++ tailWord_5969343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5969343).length < 2 ^ (prefixWord ++ tailWord_5969343).sum := by decide
  have hdescent : baseEnd_5969343 < baseStart_5969343 := by decide
  rcases family_descends (prefixWord ++ tailWord_5969343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5969364 : List Nat := [2, 4, 1, 2, 4, 1, 1, 1, 1, 1, 5]
def baseStart_5969364 : Nat := 118140960795 + 5969364 * 2 ^ 59
def prefixEnd_5969364 : Nat := 4983230072969 + 3 ^ 40 * 5969364 * 2
def baseEnd_5969364 : Nat := 3065152933645488069597401

theorem tailTrace_5969364 : CollatzResearch.WordTrace tailWord_5969364 prefixEnd_5969364 3065152933645488069597401 := by
  unfold tailWord_5969364
  simp only [CollatzResearch.WordTrace]
  refine ⟨108860295773010594525433573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145147061030680792700578097 108860295773010594525433573)
  ·
    refine ⟨20411305457439486473518795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108860295773010594525433573 20411305457439486473518795)
    ·
      refine ⟨30616958186159229710278193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20411305457439486473518795 30616958186159229710278193)
      ·
        refine ⟨22962718639619422282708645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30616958186159229710278193 22962718639619422282708645)
        ·
          refine ⟨4305509744928641678007871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22962718639619422282708645 4305509744928641678007871)
          ·
            refine ⟨6458264617392962517011807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4305509744928641678007871 6458264617392962517011807)
            ·
              refine ⟨9687396926089443775517711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6458264617392962517011807 9687396926089443775517711)
              ·
                refine ⟨14531095389134165663276567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9687396926089443775517711 14531095389134165663276567)
                ·
                  refine ⟨21796643083701248494914851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14531095389134165663276567 21796643083701248494914851)
                  ·
                    refine ⟨32694964625551872742372277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21796643083701248494914851 32694964625551872742372277)
                    ·
                      refine ⟨3065152933645488069597401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32694964625551872742372277 3065152933645488069597401)
                      ·
                        rfl

theorem cell23_5969364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_5969364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5969364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5969364 prefixEnd_5969364 := by exact prefixLift 5969364
  have htrace : WordTrace (prefixWord ++ tailWord_5969364) baseStart_5969364 baseEnd_5969364 := by
    simpa [prefixWord, tailWord_5969364, baseEnd_5969364] using wordTrace_append hprefix tailTrace_5969364
  have hstable : (prefixWord ++ tailWord_5969364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5969364).length < 2 ^ (prefixWord ++ tailWord_5969364).sum := by decide
  have hdescent : baseEnd_5969364 < baseStart_5969364 := by decide
  rcases family_descends (prefixWord ++ tailWord_5969364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5969377 : List Nat := [1, 2, 3, 1, 2, 3, 1, 4, 2, 1, 3]
def baseStart_5969377 : Nat := 118140960795 + 5969377 * 2 ^ 59
def prefixEnd_5969377 : Nat := 4983230072969 + 3 ^ 40 * 5969377 * 2
def baseEnd_5969377 : Nat := 3065159608893996518734841

theorem tailTrace_5969377 : CollatzResearch.WordTrace tailWord_5969377 prefixEnd_5969377 3065159608893996518734841 := by
  unfold tailWord_5969377
  simp only [CollatzResearch.WordTrace]
  refine ⟨217721065694974092271090385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145147377129982728180726923 217721065694974092271090385)
  ·
    refine ⟨163290799271230569203317789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217721065694974092271090385 163290799271230569203317789)
    ·
      refine ⟨61234049726711463451244171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163290799271230569203317789 61234049726711463451244171)
      ·
        refine ⟨91851074590067195176866257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61234049726711463451244171 91851074590067195176866257)
        ·
          refine ⟨68888305942550396382649693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91851074590067195176866257 68888305942550396382649693)
          ·
            refine ⟨25833114728456398643493635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68888305942550396382649693 25833114728456398643493635)
            ·
              refine ⟨38749672092684597965240453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25833114728456398643493635 38749672092684597965240453)
              ·
                refine ⟨7265563517378362118482585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38749672092684597965240453 7265563517378362118482585)
                ·
                  refine ⟨5449172638033771588861939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7265563517378362118482585 5449172638033771588861939)
                  ·
                    refine ⟨8173758957050657383292909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5449172638033771588861939 8173758957050657383292909)
                    ·
                      refine ⟨3065159608893996518734841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8173758957050657383292909 3065159608893996518734841)
                      ·
                        rfl

theorem cell23_5969377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 4, 2, 1, 3].length) (baseStart_5969377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5969377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5969377 prefixEnd_5969377 := by exact prefixLift 5969377
  have htrace : WordTrace (prefixWord ++ tailWord_5969377) baseStart_5969377 baseEnd_5969377 := by
    simpa [prefixWord, tailWord_5969377, baseEnd_5969377] using wordTrace_append hprefix tailTrace_5969377
  have hstable : (prefixWord ++ tailWord_5969377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5969377).length < 2 ^ (prefixWord ++ tailWord_5969377).sum := by decide
  have hdescent : baseEnd_5969377 < baseStart_5969377 := by decide
  rcases family_descends (prefixWord ++ tailWord_5969377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5969393 : List Nat := [1, 2, 2, 2, 3, 2, 1, 1, 1, 8]
def baseStart_5969393 : Nat := 118140960795 + 5969393 * 2 ^ 59
def prefixEnd_5969393 : Nat := 4983230072969 + 3 ^ 40 * 5969393 * 2
def baseEnd_5969393 : Nat := 1021722608194822818711589

theorem tailTrace_5969393 : CollatzResearch.WordTrace tailWord_5969393 prefixEnd_5969393 1021722608194822818711589 := by
  unfold tailWord_5969393
  simp only [CollatzResearch.WordTrace]
  refine ⟨217721649262916127003672833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145147766175277418002448555 217721649262916127003672833)
  ·
    refine ⟨163291236947187095252754625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217721649262916127003672833 163291236947187095252754625)
    ·
      refine ⟨122468427710390321439565969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163291236947187095252754625 122468427710390321439565969)
      ·
        refine ⟨91851320782792741079674477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122468427710390321439565969 91851320782792741079674477)
        ·
          refine ⟨34444245293547277904877929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91851320782792741079674477 34444245293547277904877929)
          ·
            refine ⟨25833183970160458428658447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34444245293547277904877929 25833183970160458428658447)
            ·
              refine ⟨38749775955240687642987671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25833183970160458428658447 38749775955240687642987671)
              ·
                refine ⟨58124663932861031464481507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38749775955240687642987671 58124663932861031464481507)
                ·
                  refine ⟨87186995899291547196722261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58124663932861031464481507 87186995899291547196722261)
                  ·
                    refine ⟨1021722608194822818711589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 87186995899291547196722261 1021722608194822818711589)
                    ·
                      rfl

theorem cell23_5969393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 8].length) (baseStart_5969393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5969393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5969393 prefixEnd_5969393 := by exact prefixLift 5969393
  have htrace : WordTrace (prefixWord ++ tailWord_5969393) baseStart_5969393 baseEnd_5969393 := by
    simpa [prefixWord, tailWord_5969393, baseEnd_5969393] using wordTrace_append hprefix tailTrace_5969393
  have hstable : (prefixWord ++ tailWord_5969393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5969393).length < 2 ^ (prefixWord ++ tailWord_5969393).sum := by decide
  have hdescent : baseEnd_5969393 < baseStart_5969393 := by decide
  rcases family_descends (prefixWord ++ tailWord_5969393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5969394 : List Nat := [3, 2, 1, 4, 1, 1, 2, 3, 2, 1, 3]
def baseStart_5969394 : Nat := 118140960795 + 5969394 * 2 ^ 59
def prefixEnd_5969394 : Nat := 4983230072969 + 3 ^ 40 * 5969394 * 2
def baseEnd_5969394 : Nat := 3065168338065122952222263

theorem tailTrace_5969394 : CollatzResearch.WordTrace tailWord_5969394 prefixEnd_5969394 3065168338065122952222263 := by
  unfold tailWord_5969394
  simp only [CollatzResearch.WordTrace]
  refine ⟨54430421433978126043614809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145147790490608336116306157 54430421433978126043614809)
  ·
    refine ⟨40822816075483594532711107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54430421433978126043614809 40822816075483594532711107)
    ·
      refine ⟨61234224113225391799066661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40822816075483594532711107 61234224113225391799066661)
      ·
        refine ⟨11481417021229760962324999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61234224113225391799066661 11481417021229760962324999)
        ·
          refine ⟨17222125531844641443487499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11481417021229760962324999 17222125531844641443487499)
          ·
            refine ⟨25833188297766962165231249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17222125531844641443487499 25833188297766962165231249)
            ·
              refine ⟨19374891223325221623923437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25833188297766962165231249 19374891223325221623923437)
              ·
                refine ⟨7265584208746958108971289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19374891223325221623923437 7265584208746958108971289)
                ·
                  refine ⟨5449188156560218581728467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7265584208746958108971289 5449188156560218581728467)
                  ·
                    refine ⟨8173782234840327872592701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5449188156560218581728467 8173782234840327872592701)
                    ·
                      refine ⟨3065168338065122952222263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8173782234840327872592701 3065168338065122952222263)
                      ·
                        rfl

theorem cell23_5969394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_5969394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5969394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5969394 prefixEnd_5969394 := by exact prefixLift 5969394
  have htrace : WordTrace (prefixWord ++ tailWord_5969394) baseStart_5969394 baseEnd_5969394 := by
    simpa [prefixWord, tailWord_5969394, baseEnd_5969394] using wordTrace_append hprefix tailTrace_5969394
  have hstable : (prefixWord ++ tailWord_5969394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5969394).length < 2 ^ (prefixWord ++ tailWord_5969394).sum := by decide
  have hdescent : baseEnd_5969394 < baseStart_5969394 := by decide
  rcases family_descends (prefixWord ++ tailWord_5969394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5969413 : List Nat := [1, 3, 1, 1, 2, 2, 1, 1, 3, 4, 4]
def baseStart_5969413 : Nat := 118140960795 + 5969413 * 2 ^ 59
def prefixEnd_5969413 : Nat := 4983230072969 + 3 ^ 40 * 5969413 * 2
def baseEnd_5969413 : Nat := 3065178094197558377884675

theorem tailTrace_5969413 : CollatzResearch.WordTrace tailWord_5969413 prefixEnd_5969413 3065178094197558377884675 := by
  unfold tailWord_5969413
  simp only [CollatzResearch.WordTrace]
  refine ⟨217722378722843670419400893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145148252481895780279600595 217722378722843670419400893)
  ·
    refine ⟨81645892021066376407275335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217722378722843670419400893 81645892021066376407275335)
    ·
      refine ⟨122468838031599564610913003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81645892021066376407275335 122468838031599564610913003)
      ·
        refine ⟨183703257047399346916369505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122468838031599564610913003 183703257047399346916369505)
        ·
          refine ⟨137777442785549510187277129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183703257047399346916369505 137777442785549510187277129)
          ·
            refine ⟨103333082089162132640457847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137777442785549510187277129 103333082089162132640457847)
            ·
              refine ⟨154999623133743198960686771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103333082089162132640457847 154999623133743198960686771)
              ·
                refine ⟨232499434700614798441030157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154999623133743198960686771 232499434700614798441030157)
                ·
                  refine ⟨87187288012730549415386309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 232499434700614798441030157 87187288012730549415386309)
                  ·
                    refine ⟨16347616502386978015384933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 87187288012730549415386309 16347616502386978015384933)
                    ·
                      refine ⟨3065178094197558377884675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16347616502386978015384933 3065178094197558377884675)
                      ·
                        rfl

theorem cell23_5969413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 4, 4].length) (baseStart_5969413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5969413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5969413 prefixEnd_5969413 := by exact prefixLift 5969413
  have htrace : WordTrace (prefixWord ++ tailWord_5969413) baseStart_5969413 baseEnd_5969413 := by
    simpa [prefixWord, tailWord_5969413, baseEnd_5969413] using wordTrace_append hprefix tailTrace_5969413
  have hstable : (prefixWord ++ tailWord_5969413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5969413).length < 2 ^ (prefixWord ++ tailWord_5969413).sum := by decide
  have hdescent : baseEnd_5969413 < baseStart_5969413 := by decide
  rcases family_descends (prefixWord ++ tailWord_5969413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5969417 : List Nat := [1, 2, 1, 1, 3, 1, 4, 2, 4, 2, 2]
def baseStart_5969417 : Nat := 118140960795 + 5969417 * 2 ^ 59
def prefixEnd_5969417 : Nat := 4983230072969 + 3 ^ 40 * 5969417 * 2
def baseEnd_5969417 : Nat := 3065180148120176362234657

theorem tailTrace_5969417 : CollatzResearch.WordTrace tailWord_5969417 prefixEnd_5969417 3065180148120176362234657 := by
  unfold tailWord_5969417
  simp only [CollatzResearch.WordTrace]
  refine ⟨217722524614829179102546505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145148349743219452735031003 217722524614829179102546505)
  ·
    refine ⟨163291893461121884326909879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217722524614829179102546505 163291893461121884326909879)
    ·
      refine ⟨244937840191682826490364819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163291893461121884326909879 244937840191682826490364819)
      ·
        refine ⟨367406760287524239735547229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244937840191682826490364819 367406760287524239735547229)
        ·
          refine ⟨137777535107821589900830211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 367406760287524239735547229 137777535107821589900830211)
          ·
            refine ⟨206666302661732384851245317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137777535107821589900830211 206666302661732384851245317)
            ·
              refine ⟨38749931749074822159608497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 206666302661732384851245317 38749931749074822159608497)
              ·
                refine ⟨29062448811806116619706373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38749931749074822159608497 29062448811806116619706373)
                ·
                  refine ⟨5449209152213646866194945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29062448811806116619706373 5449209152213646866194945)
                  ·
                    refine ⟨4086906864160235149646209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5449209152213646866194945 4086906864160235149646209)
                    ·
                      refine ⟨3065180148120176362234657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4086906864160235149646209 3065180148120176362234657)
                      ·
                        rfl

theorem cell23_5969417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 4, 2, 2].length) (baseStart_5969417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5969417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5969417 prefixEnd_5969417 := by exact prefixLift 5969417
  have htrace : WordTrace (prefixWord ++ tailWord_5969417) baseStart_5969417 baseEnd_5969417 := by
    simpa [prefixWord, tailWord_5969417, baseEnd_5969417] using wordTrace_append hprefix tailTrace_5969417
  have hstable : (prefixWord ++ tailWord_5969417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5969417).length < 2 ^ (prefixWord ++ tailWord_5969417).sum := by decide
  have hdescent : baseEnd_5969417 < baseStart_5969417 := by decide
  rcases family_descends (prefixWord ++ tailWord_5969417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5969428 : List Nat := [2, 4, 3, 1, 2, 2, 1, 2, 2, 1, 3]
def baseStart_5969428 : Nat := 118140960795 + 5969428 * 2 ^ 59
def prefixEnd_5969428 : Nat := 4983230072969 + 3 ^ 40 * 5969428 * 2
def baseEnd_5969428 : Nat := 3065185796407375819197107

theorem tailTrace_5969428 : CollatzResearch.WordTrace tailWord_5969428 prefixEnd_5969428 3065185796407375819197107 := by
  unfold tailWord_5969428
  simp only [CollatzResearch.WordTrace]
  refine ⟨108861462908894663990598469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145148617211859551987464625 108861462908894663990598469)
  ·
    refine ⟨20411524295417749498237213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108861462908894663990598469 20411524295417749498237213)
    ·
      refine ⟨7654321610781656061838955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20411524295417749498237213 7654321610781656061838955)
      ·
        refine ⟨11481482416172484092758433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7654321610781656061838955 11481482416172484092758433)
        ·
          refine ⟨8611111812129363069568825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11481482416172484092758433 8611111812129363069568825)
          ·
            refine ⟨6458333859097022302176619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8611111812129363069568825 6458333859097022302176619)
            ·
              refine ⟨9687500788645533453264929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6458333859097022302176619 9687500788645533453264929)
              ·
                refine ⟨7265625591484150089948697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9687500788645533453264929 7265625591484150089948697)
                ·
                  refine ⟨5449219193613112567461523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7265625591484150089948697 5449219193613112567461523)
                  ·
                    refine ⟨8173828790419668851192285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5449219193613112567461523 8173828790419668851192285)
                    ·
                      refine ⟨3065185796407375819197107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8173828790419668851192285 3065185796407375819197107)
                      ·
                        rfl

theorem cell23_5969428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_5969428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5969428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5969428 prefixEnd_5969428 := by exact prefixLift 5969428
  have htrace : WordTrace (prefixWord ++ tailWord_5969428) baseStart_5969428 baseEnd_5969428 := by
    simpa [prefixWord, tailWord_5969428, baseEnd_5969428] using wordTrace_append hprefix tailTrace_5969428
  have hstable : (prefixWord ++ tailWord_5969428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5969428).length < 2 ^ (prefixWord ++ tailWord_5969428).sum := by decide
  have hdescent : baseEnd_5969428 < baseStart_5969428 := by decide
  rcases family_descends (prefixWord ++ tailWord_5969428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5969440 : List Nat := [2, 1, 1, 6, 1, 1, 1, 3, 7]
def baseStart_5969440 : Nat := 118140960795 + 5969440 * 2 ^ 59
def prefixEnd_5969440 : Nat := 4983230072969 + 3 ^ 40 * 5969440 * 2
def baseEnd_5969440 : Nat := 340576884241692196916339

theorem tailTrace_5969440 : CollatzResearch.WordTrace tailWord_5969440 prefixEnd_5969440 340576884241692196916339 := by
  unfold tailWord_5969440
  simp only [CollatzResearch.WordTrace]
  refine ⟨108861681746872927015316887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145148908995830569353755849 108861681746872927015316887)
  ·
    refine ⟨163292522620309390522975331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108861681746872927015316887 163292522620309390522975331)
    ·
      refine ⟨244938783930464085784462997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163292522620309390522975331 244938783930464085784462997)
      ·
        refine ⟨11481505496740504021146703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 244938783930464085784462997 11481505496740504021146703)
        ·
          refine ⟨17222258245110756031720055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11481505496740504021146703 17222258245110756031720055)
          ·
            refine ⟨25833387367666134047580083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17222258245110756031720055 25833387367666134047580083)
            ·
              refine ⟨38750081051499201071370125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25833387367666134047580083 38750081051499201071370125)
              ·
                refine ⟨14531280394312200401763797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38750081051499201071370125 14531280394312200401763797)
                ·
                  refine ⟨340576884241692196916339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14531280394312200401763797 340576884241692196916339)
                  ·
                    rfl

theorem cell23_5969440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 3, 7].length) (baseStart_5969440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5969440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5969440 prefixEnd_5969440 := by exact prefixLift 5969440
  have htrace : WordTrace (prefixWord ++ tailWord_5969440) baseStart_5969440 baseEnd_5969440 := by
    simpa [prefixWord, tailWord_5969440, baseEnd_5969440] using wordTrace_append hprefix tailTrace_5969440
  have hstable : (prefixWord ++ tailWord_5969440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5969440).length < 2 ^ (prefixWord ++ tailWord_5969440).sum := by decide
  have hdescent : baseEnd_5969440 < baseStart_5969440 := by decide
  rcases family_descends (prefixWord ++ tailWord_5969440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5969557 : List Nat := [1, 3, 2, 1, 1, 1, 1, 2, 7, 1, 3]
def baseStart_5969557 : Nat := 118140960795 + 5969557 * 2 ^ 59
def prefixEnd_5969557 : Nat := 4983230072969 + 3 ^ 40 * 5969557 * 2
def baseEnd_5969557 : Nat := 3065252035411805814484013

theorem tailTrace_5969557 : CollatzResearch.WordTrace tailWord_5969557 prefixEnd_5969557 3065252035411805814484013 := by
  unfold tailWord_5969557
  simp only [CollatzResearch.WordTrace]
  refine ⟨217727630834321983012642925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145151753889547988675095283 217727630834321983012642925)
  ·
    refine ⟨81647861562870743629741097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217727630834321983012642925 81647861562870743629741097)
    ·
      refine ⟨61235896172153057722305823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81647861562870743629741097 61235896172153057722305823)
      ·
        refine ⟨91853844258229586583458735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61235896172153057722305823 91853844258229586583458735)
        ·
          refine ⟨137780766387344379875188103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91853844258229586583458735 137780766387344379875188103)
          ·
            refine ⟨206671149581016569812782155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137780766387344379875188103 206671149581016569812782155)
            ·
              refine ⟨310006724371524854719173233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206671149581016569812782155 310006724371524854719173233)
              ·
                refine ⟨232505043278643641039379925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 310006724371524854719173233 232505043278643641039379925)
                ·
                  refine ⟨5449336951843210336860467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 232505043278643641039379925 5449336951843210336860467)
                  ·
                    refine ⟨8174005427764815505290701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5449336951843210336860467 8174005427764815505290701)
                    ·
                      refine ⟨3065252035411805814484013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8174005427764815505290701 3065252035411805814484013)
                      ·
                        rfl

theorem cell23_5969557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 7, 1, 3].length) (baseStart_5969557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5969557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5969557 prefixEnd_5969557 := by exact prefixLift 5969557
  have htrace : WordTrace (prefixWord ++ tailWord_5969557) baseStart_5969557 baseEnd_5969557 := by
    simpa [prefixWord, tailWord_5969557, baseEnd_5969557] using wordTrace_append hprefix tailTrace_5969557
  have hstable : (prefixWord ++ tailWord_5969557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5969557).length < 2 ^ (prefixWord ++ tailWord_5969557).sum := by decide
  have hdescent : baseEnd_5969557 < baseStart_5969557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5969557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5969584 : List Nat := [2, 1, 1, 1, 2, 1, 7, 1, 2, 3, 2]
def baseStart_5969584 : Nat := 118140960795 + 5969584 * 2 ^ 59
def prefixEnd_5969584 : Nat := 4983230072969 + 3 ^ 40 * 5969584 * 2
def baseEnd_5969584 : Nat := 3065265899389477208846389

theorem tailTrace_5969584 : CollatzResearch.WordTrace tailWord_5969584 prefixEnd_5969584 3065265899389477208846389 := by
  unfold tailWord_5969584
  simp only [CollatzResearch.WordTrace]
  refine ⟨108864307802612083311937903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145152410403482777749250537 108864307802612083311937903)
  ·
    refine ⟨163296461703918124967906855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108864307802612083311937903 163296461703918124967906855)
    ·
      refine ⟨244944692555877187451860283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163296461703918124967906855 244944692555877187451860283)
      ·
        refine ⟨367417038833815781177790425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244944692555877187451860283 367417038833815781177790425)
        ·
          refine ⟨275562779125361835883342819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 367417038833815781177790425 275562779125361835883342819)
          ·
            refine ⟨413344168688042753825014229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275562779125361835883342819 413344168688042753825014229)
            ·
              refine ⟨9687753953626002042773771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 413344168688042753825014229 9687753953626002042773771)
              ·
                refine ⟨14531630930439003064160657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9687753953626002042773771 14531630930439003064160657)
                ·
                  refine ⟨10898723197829252298120493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14531630930439003064160657 10898723197829252298120493)
                  ·
                    refine ⟨4087021199185969611795185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10898723197829252298120493 4087021199185969611795185)
                    ·
                      refine ⟨3065265899389477208846389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4087021199185969611795185 3065265899389477208846389)
                      ·
                        rfl

theorem cell23_5969584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 1, 2, 3, 2].length) (baseStart_5969584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5969584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5969584 prefixEnd_5969584 := by exact prefixLift 5969584
  have htrace : WordTrace (prefixWord ++ tailWord_5969584) baseStart_5969584 baseEnd_5969584 := by
    simpa [prefixWord, tailWord_5969584, baseEnd_5969584] using wordTrace_append hprefix tailTrace_5969584
  have hstable : (prefixWord ++ tailWord_5969584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5969584).length < 2 ^ (prefixWord ++ tailWord_5969584).sum := by decide
  have hdescent : baseEnd_5969584 < baseStart_5969584 := by decide
  rcases family_descends (prefixWord ++ tailWord_5969584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5969591 : List Nat := [1, 1, 3, 1, 5, 1, 1, 5, 1, 1, 3]
def baseStart_5969591 : Nat := 118140960795 + 5969591 * 2 ^ 59
def prefixEnd_5969591 : Nat := 4983230072969 + 3 ^ 40 * 5969591 * 2
def baseEnd_5969591 : Nat := 3065269493754058681458857

theorem tailTrace_5969591 : CollatzResearch.WordTrace tailWord_5969591 prefixEnd_5969591 3065269493754058681458857 := by
  unfold tailWord_5969591
  simp only [CollatzResearch.WordTrace]
  refine ⟨217728870916198806819380627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145152580610799204546253751 217728870916198806819380627)
  ·
    refine ⟨326593306374298210229070941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217728870916198806819380627 326593306374298210229070941)
    ·
      refine ⟨122472489890361828835901603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 326593306374298210229070941 122472489890361828835901603)
      ·
        refine ⟨183708734835542743253852405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122472489890361828835901603 183708734835542743253852405)
        ·
          refine ⟨17222693890832132180048663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 183708734835542743253852405 17222693890832132180048663)
          ·
            refine ⟨25834040836248198270072995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17222693890832132180048663 25834040836248198270072995)
            ·
              refine ⟨38751061254372297405109493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25834040836248198270072995 38751061254372297405109493)
              ·
                refine ⟨3632911992597402881729015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38751061254372297405109493 3632911992597402881729015)
                ·
                  refine ⟨5449367988896104322593523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3632911992597402881729015 5449367988896104322593523)
                  ·
                    refine ⟨8174051983344156483890285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5449367988896104322593523 8174051983344156483890285)
                    ·
                      refine ⟨3065269493754058681458857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8174051983344156483890285 3065269493754058681458857)
                      ·
                        rfl

theorem cell23_5969591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 5, 1, 1, 3].length) (baseStart_5969591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5969591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5969591 prefixEnd_5969591 := by exact prefixLift 5969591
  have htrace : WordTrace (prefixWord ++ tailWord_5969591) baseStart_5969591 baseEnd_5969591 := by
    simpa [prefixWord, tailWord_5969591, baseEnd_5969591] using wordTrace_append hprefix tailTrace_5969591
  have hstable : (prefixWord ++ tailWord_5969591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5969591).length < 2 ^ (prefixWord ++ tailWord_5969591).sum := by decide
  have hdescent : baseEnd_5969591 < baseStart_5969591 := by decide
  rcases family_descends (prefixWord ++ tailWord_5969591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5969594 : List Nat := [3, 1, 1, 1, 2, 4, 4, 1, 1, 5]
def baseStart_5969594 : Nat := 118140960795 + 5969594 * 2 ^ 59
def prefixEnd_5969594 : Nat := 4983230072969 + 3 ^ 40 * 5969594 * 2
def baseEnd_5969594 : Nat := 1021757011398674056573781

theorem tailTrace_5969594 : CollatzResearch.WordTrace tailWord_5969594 prefixEnd_5969594 1021757011398674056573781 := by
  unfold tailWord_5969594
  simp only [CollatzResearch.WordTrace]
  refine ⟨54432245083796984582934959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145152653556791958887826557 54432245083796984582934959)
  ·
    refine ⟨81648367625695476874402439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54432245083796984582934959 81648367625695476874402439)
    ·
      refine ⟨122472551438543215311603659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81648367625695476874402439 122472551438543215311603659)
      ·
        refine ⟨183708827157814822967405489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122472551438543215311603659 183708827157814822967405489)
        ·
          refine ⟨137781620368361117225554117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183708827157814822967405489 137781620368361117225554117)
          ·
            refine ⟨25834053819067709479791397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 137781620368361117225554117 25834053819067709479791397)
            ·
              refine ⟨4843885091075195527460887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25834053819067709479791397 4843885091075195527460887)
              ·
                refine ⟨7265827636612793291191331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4843885091075195527460887 7265827636612793291191331)
                ·
                  refine ⟨10898741454919189936786997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7265827636612793291191331 10898741454919189936786997)
                  ·
                    refine ⟨1021757011398674056573781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10898741454919189936786997 1021757011398674056573781)
                    ·
                      rfl

theorem cell23_5969594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4, 1, 1, 5].length) (baseStart_5969594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5969594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5969594 prefixEnd_5969594 := by exact prefixLift 5969594
  have htrace : WordTrace (prefixWord ++ tailWord_5969594) baseStart_5969594 baseEnd_5969594 := by
    simpa [prefixWord, tailWord_5969594, baseEnd_5969594] using wordTrace_append hprefix tailTrace_5969594
  have hstable : (prefixWord ++ tailWord_5969594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5969594).length < 2 ^ (prefixWord ++ tailWord_5969594).sum := by decide
  have hdescent : baseEnd_5969594 < baseStart_5969594 := by decide
  rcases family_descends (prefixWord ++ tailWord_5969594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5969607 : List Nat := [1, 1, 4, 1, 1, 1, 5, 1, 4, 4]
def baseStart_5969607 : Nat := 118140960795 + 5969607 * 2 ^ 59
def prefixEnd_5969607 : Nat := 4983230072969 + 3 ^ 40 * 5969607 * 2
def baseEnd_5969607 : Nat := 1021759236481510206286261

theorem tailTrace_5969607 : CollatzResearch.WordTrace tailWord_5969607 prefixEnd_5969607 1021759236481510206286261 := by
  unfold tailWord_5969607
  simp only [CollatzResearch.WordTrace]
  refine ⟨217729454484140841551963075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145152969656093894367975383 217729454484140841551963075)
  ·
    refine ⟨326594181726211262327944613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217729454484140841551963075 326594181726211262327944613)
    ·
      refine ⟨61236409073664611686489615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 326594181726211262327944613 61236409073664611686489615)
      ·
        refine ⟨91854613610496917529734423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61236409073664611686489615 91854613610496917529734423)
        ·
          refine ⟨137781920415745376294601635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91854613610496917529734423 137781920415745376294601635)
          ·
            refine ⟨206672880623618064441902453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137781920415745376294601635 206672880623618064441902453)
            ·
              refine ⟨19375582558464193541428355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 206672880623618064441902453 19375582558464193541428355)
              ·
                refine ⟨29063373837696290312142533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19375582558464193541428355 29063373837696290312142533)
                ·
                  refine ⟨5449382594568054433526725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29063373837696290312142533 5449382594568054433526725)
                  ·
                    refine ⟨1021759236481510206286261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5449382594568054433526725 1021759236481510206286261)
                    ·
                      rfl

theorem cell23_5969607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 4, 4].length) (baseStart_5969607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5969607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5969607 prefixEnd_5969607 := by exact prefixLift 5969607
  have htrace : WordTrace (prefixWord ++ tailWord_5969607) baseStart_5969607 baseEnd_5969607 := by
    simpa [prefixWord, tailWord_5969607, baseEnd_5969607] using wordTrace_append hprefix tailTrace_5969607
  have hstable : (prefixWord ++ tailWord_5969607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5969607).length < 2 ^ (prefixWord ++ tailWord_5969607).sum := by decide
  have hdescent : baseEnd_5969607 < baseStart_5969607 := by decide
  rcases family_descends (prefixWord ++ tailWord_5969607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5969617 : List Nat := [1, 2, 2, 1, 2, 5, 1, 2, 1, 1, 5]
def baseStart_5969617 : Nat := 118140960795 + 5969617 * 2 ^ 59
def prefixEnd_5969617 : Nat := 4983230072969 + 3 ^ 40 * 5969617 * 2
def baseEnd_5969617 : Nat := 3065282844251075579733737

theorem tailTrace_5969617 : CollatzResearch.WordTrace tailWord_5969617 prefixEnd_5969617 3065282844251075579733737 := by
  unfold tailWord_5969617
  simp only [CollatzResearch.WordTrace]
  refine ⟨217729819214104613259827105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145153212809403075506551403 217729819214104613259827105)
  ·
    refine ⟨163297364410578459944870329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217729819214104613259827105 163297364410578459944870329)
    ·
      refine ⟨122473023307933844958652747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163297364410578459944870329 122473023307933844958652747)
      ·
        refine ⟨183709534961900767437979121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122473023307933844958652747 183709534961900767437979121)
        ·
          refine ⟨137782151221425575578484341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183709534961900767437979121 137782151221425575578484341)
          ·
            refine ⟨12917076677008647710482907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 137782151221425575578484341 12917076677008647710482907)
            ·
              refine ⟨19375615015512971565724361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12917076677008647710482907 19375615015512971565724361)
              ·
                refine ⟨14531711261634728674293271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19375615015512971565724361 14531711261634728674293271)
                ·
                  refine ⟨21797566892452093011439907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14531711261634728674293271 21797566892452093011439907)
                  ·
                    refine ⟨32696350338678139517159861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21797566892452093011439907 32696350338678139517159861)
                    ·
                      refine ⟨3065282844251075579733737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32696350338678139517159861 3065282844251075579733737)
                      ·
                        rfl

theorem cell23_5969617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 2, 1, 1, 5].length) (baseStart_5969617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5969617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5969617 prefixEnd_5969617 := by exact prefixLift 5969617
  have htrace : WordTrace (prefixWord ++ tailWord_5969617) baseStart_5969617 baseEnd_5969617 := by
    simpa [prefixWord, tailWord_5969617, baseEnd_5969617] using wordTrace_append hprefix tailTrace_5969617
  have hstable : (prefixWord ++ tailWord_5969617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5969617).length < 2 ^ (prefixWord ++ tailWord_5969617).sum := by decide
  have hdescent : baseEnd_5969617 < baseStart_5969617 := by decide
  rcases family_descends (prefixWord ++ tailWord_5969617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5969647 : List Nat := [1, 1, 2, 1, 5, 1, 2, 1, 3, 3, 3]
def baseStart_5969647 : Nat := 118140960795 + 5969647 * 2 ^ 59
def prefixEnd_5969647 : Nat := 4983230072969 + 3 ^ 40 * 5969647 * 2
def baseEnd_5969647 : Nat := 3065298248670710462358599

theorem tailTrace_5969647 : CollatzResearch.WordTrace tailWord_5969647 prefixEnd_5969647 3065298248670710462358599 := by
  unfold tailWord_5969647
  simp only [CollatzResearch.WordTrace]
  refine ⟨217730913403995928383419195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145153942269330618922279463 217730913403995928383419195)
  ·
    refine ⟨326596370105993892575128793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217730913403995928383419195 326596370105993892575128793)
    ·
      refine ⟨244947277579495419431346595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326596370105993892575128793 244947277579495419431346595)
      ·
        refine ⟨367420916369243129147019893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244947277579495419431346595 367420916369243129147019893)
        ·
          refine ⟨34445710909616543357533115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 367420916369243129147019893 34445710909616543357533115)
          ·
            refine ⟨51668566364424815036299673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34445710909616543357533115 51668566364424815036299673)
            ·
              refine ⟨38751424773318611277224755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51668566364424815036299673 38751424773318611277224755)
              ·
                refine ⟨58127137159977916915837133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38751424773318611277224755 58127137159977916915837133)
                ·
                  refine ⟨21797676434991718843438925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58127137159977916915837133 21797676434991718843438925)
                  ·
                    refine ⟨8174128663121894566289597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21797676434991718843438925 8174128663121894566289597)
                    ·
                      refine ⟨3065298248670710462358599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8174128663121894566289597 3065298248670710462358599)
                      ·
                        rfl

theorem cell23_5969647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 3, 3, 3].length) (baseStart_5969647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5969647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5969647 prefixEnd_5969647 := by exact prefixLift 5969647
  have htrace : WordTrace (prefixWord ++ tailWord_5969647) baseStart_5969647 baseEnd_5969647 := by
    simpa [prefixWord, tailWord_5969647, baseEnd_5969647] using wordTrace_append hprefix tailTrace_5969647
  have hstable : (prefixWord ++ tailWord_5969647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5969647).length < 2 ^ (prefixWord ++ tailWord_5969647).sum := by decide
  have hdescent : baseEnd_5969647 < baseStart_5969647 := by decide
  rcases family_descends (prefixWord ++ tailWord_5969647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5969708 : List Nat := [2, 2, 1, 1, 1, 6, 3, 1, 1, 3, 2]
def baseStart_5969708 : Nat := 118140960795 + 5969708 * 2 ^ 59
def prefixEnd_5969708 : Nat := 4983230072969 + 3 ^ 40 * 5969708 * 2
def baseEnd_5969708 : Nat := 3065329570990634723695819

theorem tailTrace_5969708 : CollatzResearch.WordTrace tailWord_5969708 prefixEnd_5969708 3065329570990634723695819 := by
  unfold tailWord_5969708
  simp only [CollatzResearch.WordTrace]
  refine ⟨108866569128387467900694889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145155425504516623867593185 108866569128387467900694889)
  ·
    refine ⟨81649926846290600925521167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108866569128387467900694889 81649926846290600925521167)
    ·
      refine ⟨122474890269435901388281751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81649926846290600925521167 122474890269435901388281751)
      ·
        refine ⟨183712335404153852082422627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122474890269435901388281751 183712335404153852082422627)
        ·
          refine ⟨275568503106230778123633941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183712335404153852082422627 275568503106230778123633941)
          ·
            refine ⟨12917273583104567724545341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 275568503106230778123633941 12917273583104567724545341)
            ·
              refine ⟨4843977593664212896704503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12917273583104567724545341 4843977593664212896704503)
              ·
                refine ⟨7265966390496319345056755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4843977593664212896704503 7265966390496319345056755)
                ·
                  refine ⟨10898949585744479017585133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7265966390496319345056755 10898949585744479017585133)
                  ·
                    refine ⟨4087106094654179631594425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10898949585744479017585133 4087106094654179631594425)
                    ·
                      refine ⟨3065329570990634723695819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4087106094654179631594425 3065329570990634723695819)
                      ·
                        rfl

theorem cell23_5969708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 3, 2].length) (baseStart_5969708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5969708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5969708 prefixEnd_5969708 := by exact prefixLift 5969708
  have htrace : WordTrace (prefixWord ++ tailWord_5969708) baseStart_5969708 baseEnd_5969708 := by
    simpa [prefixWord, tailWord_5969708, baseEnd_5969708] using wordTrace_append hprefix tailTrace_5969708
  have hstable : (prefixWord ++ tailWord_5969708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5969708).length < 2 ^ (prefixWord ++ tailWord_5969708).sum := by decide
  have hdescent : baseEnd_5969708 < baseStart_5969708 := by decide
  rcases family_descends (prefixWord ++ tailWord_5969708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5969817 : List Nat := [1, 2, 1, 2, 1, 3, 3, 2, 8]
def baseStart_5969817 : Nat := 118140960795 + 5969817 * 2 ^ 59
def prefixEnd_5969817 : Nat := 4983230072969 + 3 ^ 40 * 5969817 * 2
def baseEnd_5969817 : Nat := 340598393375774977470313

theorem tailTrace_5969817 : CollatzResearch.WordTrace tailWord_5969817 prefixEnd_5969817 340598393375774977470313 := by
  unfold tailWord_5969817
  simp only [CollatzResearch.WordTrace]
  refine ⟨217737113813380047417107705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145158075875586698278071803 217737113813380047417107705)
  ·
    refine ⟨163302835360035035562830779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217737113813380047417107705 163302835360035035562830779)
    ·
      refine ⟨244954253040052553344246169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163302835360035035562830779 244954253040052553344246169)
      ·
        refine ⟨183715689780039415008184627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244954253040052553344246169 183715689780039415008184627)
        ·
          refine ⟨275573534670059122512276941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183715689780039415008184627 275573534670059122512276941)
          ·
            refine ⟨103340075501272170942103853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 275573534670059122512276941 103340075501272170942103853)
            ·
              refine ⟨38752528312977064103288945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103340075501272170942103853 38752528312977064103288945)
              ·
                refine ⟨29064396234732798077466709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38752528312977064103288945 29064396234732798077466709)
                ·
                  refine ⟨340598393375774977470313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29064396234732798077466709 340598393375774977470313)
                  ·
                    rfl

theorem cell23_5969817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 8].length) (baseStart_5969817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5969817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5969817 prefixEnd_5969817 := by exact prefixLift 5969817
  have htrace : WordTrace (prefixWord ++ tailWord_5969817) baseStart_5969817 baseEnd_5969817 := by
    simpa [prefixWord, tailWord_5969817, baseEnd_5969817] using wordTrace_append hprefix tailTrace_5969817
  have hstable : (prefixWord ++ tailWord_5969817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5969817).length < 2 ^ (prefixWord ++ tailWord_5969817).sum := by decide
  have hdescent : baseEnd_5969817 < baseStart_5969817 := by decide
  rcases family_descends (prefixWord ++ tailWord_5969817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5969831 : List Nat := [1, 1, 6, 1, 2, 1, 1, 1, 4, 2, 3]
def baseStart_5969831 : Nat := 118140960795 + 5969831 * 2 ^ 59
def prefixEnd_5969831 : Nat := 4983230072969 + 3 ^ 40 * 5969831 * 2
def baseEnd_5969831 : Nat := 3065392729111137742457753

theorem tailTrace_5969831 : CollatzResearch.WordTrace tailWord_5969831 prefixEnd_5969831 3065392729111137742457753 := by
  unfold tailWord_5969831
  simp only [CollatzResearch.WordTrace]
  refine ⟨217737624435329327808117347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145158416290219551872078231 217737624435329327808117347)
  ·
    refine ⟨326606436652993991712176021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217737624435329327808117347 326606436652993991712176021)
    ·
      refine ⟨15309676718109093361508251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 326606436652993991712176021 15309676718109093361508251)
      ·
        refine ⟨22964515077163640042262377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15309676718109093361508251 22964515077163640042262377)
        ·
          refine ⟨17223386307872730031696783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22964515077163640042262377 17223386307872730031696783)
          ·
            refine ⟨25835079461809095047545175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17223386307872730031696783 25835079461809095047545175)
            ·
              refine ⟨38752619192713642571317763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25835079461809095047545175 38752619192713642571317763)
              ·
                refine ⟨58128928789070463856976645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38752619192713642571317763 58128928789070463856976645)
                ·
                  refine ⟨10899174147950711973183121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58128928789070463856976645 10899174147950711973183121)
                  ·
                    refine ⟨8174380610963033979887341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10899174147950711973183121 8174380610963033979887341)
                    ·
                      refine ⟨3065392729111137742457753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8174380610963033979887341 3065392729111137742457753)
                      ·
                        rfl

theorem cell23_5969831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_5969831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5969831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5969831 prefixEnd_5969831 := by exact prefixLift 5969831
  have htrace : WordTrace (prefixWord ++ tailWord_5969831) baseStart_5969831 baseEnd_5969831 := by
    simpa [prefixWord, tailWord_5969831, baseEnd_5969831] using wordTrace_append hprefix tailTrace_5969831
  have hstable : (prefixWord ++ tailWord_5969831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5969831).length < 2 ^ (prefixWord ++ tailWord_5969831).sum := by decide
  have hdescent : baseEnd_5969831 < baseStart_5969831 := by decide
  rcases family_descends (prefixWord ++ tailWord_5969831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5969847 : List Nat := [1, 1, 3, 1, 3, 1, 1, 1, 2, 9]
def baseStart_5969847 : Nat := 118140960795 + 5969847 * 2 ^ 59
def prefixEnd_5969847 : Nat := 4983230072969 + 3 ^ 40 * 5969847 * 2
def baseEnd_5969847 : Nat := 1021800314933869893285893

theorem tailTrace_5969847 : CollatzResearch.WordTrace tailWord_5969847 prefixEnd_5969847 1021800314933869893285893 := by
  unfold tailWord_5969847
  simp only [CollatzResearch.WordTrace]
  refine ⟨217738208003271362540699795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145158805335514241693799863 217738208003271362540699795)
  ·
    refine ⟨326607312004907043811049693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217738208003271362540699795 326607312004907043811049693)
    ·
      refine ⟨122477742001840141429143635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 326607312004907043811049693 122477742001840141429143635)
      ·
        refine ⟨183716613002760212143715453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122477742001840141429143635 183716613002760212143715453)
        ·
          refine ⟨68893729876035079553893295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183716613002760212143715453 68893729876035079553893295)
          ·
            refine ⟨103340594814052619330839943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68893729876035079553893295 103340594814052619330839943)
            ·
              refine ⟨155010892221078928996259915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103340594814052619330839943 155010892221078928996259915)
              ·
                refine ⟨232516338331618393494389873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155010892221078928996259915 232516338331618393494389873)
                ·
                  refine ⟨174387253748713795120792405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 232516338331618393494389873 174387253748713795120792405)
                  ·
                    refine ⟨1021800314933869893285893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 174387253748713795120792405 1021800314933869893285893)
                    ·
                      rfl

theorem cell23_5969847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 9].length) (baseStart_5969847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5969847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5969847 prefixEnd_5969847 := by exact prefixLift 5969847
  have htrace : WordTrace (prefixWord ++ tailWord_5969847) baseStart_5969847 baseEnd_5969847 := by
    simpa [prefixWord, tailWord_5969847, baseEnd_5969847] using wordTrace_append hprefix tailTrace_5969847
  have hstable : (prefixWord ++ tailWord_5969847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5969847).length < 2 ^ (prefixWord ++ tailWord_5969847).sum := by decide
  have hdescent : baseEnd_5969847 < baseStart_5969847 := by decide
  rcases family_descends (prefixWord ++ tailWord_5969847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5969904 : List Nat := [2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 5]
def baseStart_5969904 : Nat := 118140960795 + 5969904 * 2 ^ 59
def prefixEnd_5969904 : Nat := 4983230072969 + 3 ^ 40 * 5969904 * 2
def baseEnd_5969904 : Nat := 3065430213198915956844917

theorem tailTrace_5969904 : CollatzResearch.WordTrace tailWord_5969904 prefixEnd_5969904 3065430213198915956844917 := by
  unfold tailWord_5969904
  simp only [CollatzResearch.WordTrace]
  refine ⟨108870143482032430637762383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145160191309376574183683177 108870143482032430637762383)
  ·
    refine ⟨163305215223048645956643575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108870143482032430637762383 163305215223048645956643575)
    ·
      refine ⟨244957822834572968934965363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163305215223048645956643575 244957822834572968934965363)
      ·
        refine ⟨367436734251859453402448045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244957822834572968934965363 367436734251859453402448045)
        ·
          refine ⟨137788775344447295025918017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 367436734251859453402448045 137788775344447295025918017)
          ·
            refine ⟨103341581508335471269438513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137788775344447295025918017 103341581508335471269438513)
            ·
              refine ⟨77506186131251603452078885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103341581508335471269438513 77506186131251603452078885)
              ·
                refine ⟨14532409899609675647264791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77506186131251603452078885 14532409899609675647264791)
                ·
                  refine ⟨21798614849414513470897187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14532409899609675647264791 21798614849414513470897187)
                  ·
                    refine ⟨32697922274121770206345781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21798614849414513470897187 32697922274121770206345781)
                    ·
                      refine ⟨3065430213198915956844917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32697922274121770206345781 3065430213198915956844917)
                      ·
                        rfl

theorem cell23_5969904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 5].length) (baseStart_5969904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5969904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5969904 prefixEnd_5969904 := by exact prefixLift 5969904
  have htrace : WordTrace (prefixWord ++ tailWord_5969904) baseStart_5969904 baseEnd_5969904 := by
    simpa [prefixWord, tailWord_5969904, baseEnd_5969904] using wordTrace_append hprefix tailTrace_5969904
  have hstable : (prefixWord ++ tailWord_5969904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5969904).length < 2 ^ (prefixWord ++ tailWord_5969904).sum := by decide
  have hdescent : baseEnd_5969904 < baseStart_5969904 := by decide
  rcases family_descends (prefixWord ++ tailWord_5969904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5969918 : List Nat := [4, 2, 2, 2, 1, 1, 2, 1, 3, 1, 4]
def baseStart_5969918 : Nat := 118140960795 + 5969918 * 2 ^ 59
def prefixEnd_5969918 : Nat := 4983230072969 + 3 ^ 40 * 5969918 * 2
def baseEnd_5969918 : Nat := 3065437401928078902069853

theorem tailTrace_5969918 : CollatzResearch.WordTrace tailWord_5969918 prefixEnd_5969918 3065437401928078902069853 := by
  unfold tailWord_5969918
  simp only [CollatzResearch.WordTrace]
  refine ⟨27217599698251767708316801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145160531724009427777689605 27217599698251767708316801)
  ·
    refine ⟨20413199773688825781237601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27217599698251767708316801 20413199773688825781237601)
    ·
      refine ⟨15309899830266619335928201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20413199773688825781237601 15309899830266619335928201)
      ·
        refine ⟨11482424872699964501946151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15309899830266619335928201 11482424872699964501946151)
        ·
          refine ⟨17223637309049946752919227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11482424872699964501946151 17223637309049946752919227)
          ·
            refine ⟨25835455963574920129378841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17223637309049946752919227 25835455963574920129378841)
            ·
              refine ⟨19376591972681190097034131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25835455963574920129378841 19376591972681190097034131)
              ·
                refine ⟨29064887959021785145551197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19376591972681190097034131 29064887959021785145551197)
                ·
                  refine ⟨10899332984633169429581699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29064887959021785145551197 10899332984633169429581699)
                  ·
                    refine ⟨16348999476949754144372549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10899332984633169429581699 16348999476949754144372549)
                    ·
                      refine ⟨3065437401928078902069853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16348999476949754144372549 3065437401928078902069853)
                      ·
                        rfl

theorem cell23_5969918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_5969918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5969918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5969918 prefixEnd_5969918 := by exact prefixLift 5969918
  have htrace : WordTrace (prefixWord ++ tailWord_5969918) baseStart_5969918 baseEnd_5969918 := by
    simpa [prefixWord, tailWord_5969918, baseEnd_5969918] using wordTrace_append hprefix tailTrace_5969918
  have hstable : (prefixWord ++ tailWord_5969918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5969918).length < 2 ^ (prefixWord ++ tailWord_5969918).sum := by decide
  have hdescent : baseEnd_5969918 < baseStart_5969918 := by decide
  rcases family_descends (prefixWord ++ tailWord_5969918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5969921 : List Nat := [1, 2, 4, 1, 2, 1, 1, 3, 3, 2, 3]
def baseStart_5969921 : Nat := 118140960795 + 5969921 * 2 ^ 59
def prefixEnd_5969921 : Nat := 4983230072969 + 3 ^ 40 * 5969921 * 2
def baseEnd_5969921 : Nat := 3065438942370042390332339

theorem tailTrace_5969921 : CollatzResearch.WordTrace tailWord_5969921 prefixEnd_5969921 3065438942370042390332339 := by
  unfold tailWord_5969921
  simp only [CollatzResearch.WordTrace]
  refine ⟨217740907005003273178893617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145160604670002182119262411 217740907005003273178893617)
  ·
    refine ⟨163305680253752454884170213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217740907005003273178893617 163305680253752454884170213)
    ·
      refine ⟨30619815047578585290781915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163305680253752454884170213 30619815047578585290781915)
      ·
        refine ⟨45929722571367877936172873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30619815047578585290781915 45929722571367877936172873)
        ·
          refine ⟨34447291928525908452129655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45929722571367877936172873 34447291928525908452129655)
          ·
            refine ⟨51670937892788862678194483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34447291928525908452129655 51670937892788862678194483)
            ·
              refine ⟨77506406839183294017291725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51670937892788862678194483 77506406839183294017291725)
              ·
                refine ⟨29064902564693735256484397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77506406839183294017291725 29064902564693735256484397)
                ·
                  refine ⟨10899338461760150721181649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29064902564693735256484397 10899338461760150721181649)
                  ·
                    refine ⟨8174503846320113040886237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10899338461760150721181649 8174503846320113040886237)
                    ·
                      refine ⟨3065438942370042390332339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8174503846320113040886237 3065438942370042390332339)
                      ·
                        rfl

theorem cell23_5969921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_5969921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5969921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5969921 prefixEnd_5969921 := by exact prefixLift 5969921
  have htrace : WordTrace (prefixWord ++ tailWord_5969921) baseStart_5969921 baseEnd_5969921 := by
    simpa [prefixWord, tailWord_5969921, baseEnd_5969921] using wordTrace_append hprefix tailTrace_5969921
  have hstable : (prefixWord ++ tailWord_5969921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5969921).length < 2 ^ (prefixWord ++ tailWord_5969921).sum := by decide
  have hdescent : baseEnd_5969921 < baseStart_5969921 := by decide
  rcases family_descends (prefixWord ++ tailWord_5969921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5969968 : List Nat := [2, 1, 1, 1, 2, 7, 1, 1, 1, 3, 3]
def baseStart_5969968 : Nat := 118140960795 + 5969968 * 2 ^ 59
def prefixEnd_5969968 : Nat := 4983230072969 + 3 ^ 40 * 5969968 * 2
def baseEnd_5969968 : Nat := 3065463075960803706444623

theorem tailTrace_5969968 : CollatzResearch.WordTrace tailWord_5969968 prefixEnd_5969968 3065463075960803706444623 := by
  unfold tailWord_5969968
  simp only [CollatzResearch.WordTrace]
  refine ⟨108871310617916500102927279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145161747490555333470569705 108871310617916500102927279)
  ·
    refine ⟨163306965926874750154390919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108871310617916500102927279 163306965926874750154390919)
    ·
      refine ⟨244960448890312125231586379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163306965926874750154390919 244960448890312125231586379)
      ·
        refine ⟨367440673335468187847379569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244960448890312125231586379 367440673335468187847379569)
        ·
          refine ⟨275580505001601140885534677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 367440673335468187847379569 275580505001601140885534677)
          ·
            refine ⟨6458918085975026739504719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 275580505001601140885534677 6458918085975026739504719)
            ·
              refine ⟨9688377128962540109257079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6458918085975026739504719 9688377128962540109257079)
              ·
                refine ⟨14532565693443810163885619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9688377128962540109257079 14532565693443810163885619)
                ·
                  refine ⟨21798848540165715245828429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14532565693443810163885619 21798848540165715245828429)
                  ·
                    refine ⟨8174568202562143217185661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21798848540165715245828429 8174568202562143217185661)
                    ·
                      refine ⟨3065463075960803706444623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8174568202562143217185661 3065463075960803706444623)
                      ·
                        rfl

theorem cell23_5969968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 1, 1, 3, 3].length) (baseStart_5969968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5969968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5969968 prefixEnd_5969968 := by exact prefixLift 5969968
  have htrace : WordTrace (prefixWord ++ tailWord_5969968) baseStart_5969968 baseEnd_5969968 := by
    simpa [prefixWord, tailWord_5969968, baseEnd_5969968] using wordTrace_append hprefix tailTrace_5969968
  have hstable : (prefixWord ++ tailWord_5969968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5969968).length < 2 ^ (prefixWord ++ tailWord_5969968).sum := by decide
  have hdescent : baseEnd_5969968 < baseStart_5969968 := by decide
  rcases family_descends (prefixWord ++ tailWord_5969968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5969972 : List Nat := [2, 5, 1, 2, 2, 1, 2, 2, 1, 2, 3]
def baseStart_5969972 : Nat := 118140960795 + 5969972 * 2 ^ 59
def prefixEnd_5969972 : Nat := 4983230072969 + 3 ^ 40 * 5969972 * 2
def baseEnd_5969972 : Nat := 3065465129883421690794605

theorem tailTrace_5969972 : CollatzResearch.WordTrace tailWord_5969972 prefixEnd_5969972 3065465129883421690794605 := by
  unfold tailWord_5969972
  simp only [CollatzResearch.WordTrace]
  refine ⟨108871383563909254444500085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145161844751879005926000113 108871383563909254444500085)
  ·
    refine ⟨10206692209116492604171883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108871383563909254444500085 10206692209116492604171883)
    ·
      refine ⟨15310038313674738906257825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10206692209116492604171883 15310038313674738906257825)
      ·
        refine ⟨11482528735256054179693369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15310038313674738906257825 11482528735256054179693369)
        ·
          refine ⟨8611896551442040634770027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11482528735256054179693369 8611896551442040634770027)
          ·
            refine ⟨12917844827163060952155041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8611896551442040634770027 12917844827163060952155041)
            ·
              refine ⟨9688383620372295714116281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12917844827163060952155041 9688383620372295714116281)
              ·
                refine ⟨7266287715279221785587211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9688383620372295714116281 7266287715279221785587211)
                ·
                  refine ⟨10899431572918832678380817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7266287715279221785587211 10899431572918832678380817)
                  ·
                    refine ⟨8174573679689124508785613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10899431572918832678380817 8174573679689124508785613)
                    ·
                      refine ⟨3065465129883421690794605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8174573679689124508785613 3065465129883421690794605)
                      ·
                        rfl

theorem cell23_5969972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_5969972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5969972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5969972 prefixEnd_5969972 := by exact prefixLift 5969972
  have htrace : WordTrace (prefixWord ++ tailWord_5969972) baseStart_5969972 baseEnd_5969972 := by
    simpa [prefixWord, tailWord_5969972, baseEnd_5969972] using wordTrace_append hprefix tailTrace_5969972
  have hstable : (prefixWord ++ tailWord_5969972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5969972).length < 2 ^ (prefixWord ++ tailWord_5969972).sum := by decide
  have hdescent : baseEnd_5969972 < baseStart_5969972 := by decide
  rcases family_descends (prefixWord ++ tailWord_5969972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5970025 : List Nat := [1, 2, 1, 1, 1, 5, 3, 3, 2, 2, 2]
def baseStart_5970025 : Nat := 118140960795 + 5970025 * 2 ^ 59
def prefixEnd_5970025 : Nat := 4983230072969 + 3 ^ 40 * 5970025 * 2
def baseEnd_5970025 : Nat := 3065492344358109983431861

theorem tailTrace_5970025 : CollatzResearch.WordTrace tailWord_5970025 prefixEnd_5970025 3065492344358109983431861 := by
  unfold tailWord_5970025
  simp only [CollatzResearch.WordTrace]
  refine ⟨217744700196626498940679529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145163133464417665960453019 217744700196626498940679529)
  ·
    refine ⟨163308525147469874205509647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217744700196626498940679529 163308525147469874205509647)
    ·
      refine ⟨244962787721204811308264471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163308525147469874205509647 244962787721204811308264471)
      ·
        refine ⟨367444181581807216962396707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244962787721204811308264471 367444181581807216962396707)
        ·
          refine ⟨551166272372710825443595061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367444181581807216962396707 551166272372710825443595061)
          ·
            refine ⟨51671838034941639885337037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 551166272372710825443595061 51671838034941639885337037)
            ·
              refine ⟨19376939263103114957001389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51671838034941639885337037 19376939263103114957001389)
              ·
                refine ⟨7266352223663668108875521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19376939263103114957001389 7266352223663668108875521)
                ·
                  refine ⟨5449764167747751081656641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7266352223663668108875521 5449764167747751081656641)
                  ·
                    refine ⟨4087323125810813311242481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5449764167747751081656641 4087323125810813311242481)
                    ·
                      refine ⟨3065492344358109983431861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4087323125810813311242481 3065492344358109983431861)
                      ·
                        rfl

theorem cell23_5970025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 3, 2, 2, 2].length) (baseStart_5970025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5970025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5970025 prefixEnd_5970025 := by exact prefixLift 5970025
  have htrace : WordTrace (prefixWord ++ tailWord_5970025) baseStart_5970025 baseEnd_5970025 := by
    simpa [prefixWord, tailWord_5970025, baseEnd_5970025] using wordTrace_append hprefix tailTrace_5970025
  have hstable : (prefixWord ++ tailWord_5970025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5970025).length < 2 ^ (prefixWord ++ tailWord_5970025).sum := by decide
  have hdescent : baseEnd_5970025 < baseStart_5970025 := by decide
  rcases family_descends (prefixWord ++ tailWord_5970025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5970098 : List Nat := [3, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2]
def baseStart_5970098 : Nat := 118140960795 + 5970098 * 2 ^ 59
def prefixEnd_5970098 : Nat := 4983230072969 + 3 ^ 40 * 5970098 * 2
def baseEnd_5970098 : Nat := 3065529828445888197819025

theorem tailTrace_5970098 : CollatzResearch.WordTrace tailWord_5970098 prefixEnd_5970098 3065529828445888197819025 := by
  unfold tailWord_5970098
  simp only [CollatzResearch.WordTrace]
  refine ⟨54436840681340508102021737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145164908483574688272057965 54436840681340508102021737)
  ·
    refine ⟨40827630511005381076516303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54436840681340508102021737 40827630511005381076516303)
    ·
      refine ⟨61241445766508071614774455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40827630511005381076516303 61241445766508071614774455)
      ·
        refine ⟨91862168649762107422161683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61241445766508071614774455 91862168649762107422161683)
        ·
          refine ⟨137793252974643161133242525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91862168649762107422161683 137793252974643161133242525)
          ·
            refine ⟨51672469865491185424965947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137793252974643161133242525 51672469865491185424965947)
            ·
              refine ⟨77508704798236778137448921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51672469865491185424965947 77508704798236778137448921)
              ·
                refine ⟨58131528598677583603086691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77508704798236778137448921 58131528598677583603086691)
                ·
                  refine ⟨87197292898016375404630037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58131528598677583603086691 87197292898016375404630037)
                  ·
                    refine ⟨4087373104594517597092033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 87197292898016375404630037 4087373104594517597092033)
                    ·
                      refine ⟨3065529828445888197819025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4087373104594517597092033 3065529828445888197819025)
                      ·
                        rfl

theorem cell23_5970098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2].length) (baseStart_5970098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5970098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5970098 prefixEnd_5970098 := by exact prefixLift 5970098
  have htrace : WordTrace (prefixWord ++ tailWord_5970098) baseStart_5970098 baseEnd_5970098 := by
    simpa [prefixWord, tailWord_5970098, baseEnd_5970098] using wordTrace_append hprefix tailTrace_5970098
  have hstable : (prefixWord ++ tailWord_5970098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5970098).length < 2 ^ (prefixWord ++ tailWord_5970098).sum := by decide
  have hdescent : baseEnd_5970098 < baseStart_5970098 := by decide
  rcases family_descends (prefixWord ++ tailWord_5970098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5970121 : List Nat := [1, 2, 1, 1, 2, 1, 1, 8, 6]
def baseStart_5970121 : Nat := 118140960795 + 5970121 * 2 ^ 59
def prefixEnd_5970121 : Nat := 4983230072969 + 3 ^ 40 * 5970121 * 2
def baseEnd_5970121 : Nat := 340615737611215734203491

theorem tailTrace_5970121 : CollatzResearch.WordTrace tailWord_5970121 prefixEnd_5970121 340615737611215734203491 := by
  unfold tailWord_5970121
  simp only [CollatzResearch.WordTrace]
  refine ⟨217748201604278707336174217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145165467736185804890782811 217748201604278707336174217)
  ·
    refine ⟨163311151203209030502130663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217748201604278707336174217 163311151203209030502130663)
    ·
      refine ⟨244966726804813545753195995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163311151203209030502130663 244966726804813545753195995)
      ·
        refine ⟨367450090207220318629793993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244966726804813545753195995 367450090207220318629793993)
        ·
          refine ⟨275587567655415238972345495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 367450090207220318629793993 275587567655415238972345495)
          ·
            refine ⟨413381351483122858458518243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275587567655415238972345495 413381351483122858458518243)
            ·
              refine ⟨620072027224684287687777365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 413381351483122858458518243 620072027224684287687777365)
              ·
                refine ⟨7266469069039268996341141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 620072027224684287687777365 7266469069039268996341141)
                ·
                  refine ⟨340615737611215734203491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7266469069039268996341141 340615737611215734203491)
                  ·
                    rfl

theorem cell23_5970121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 8, 6].length) (baseStart_5970121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5970121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5970121 prefixEnd_5970121 := by exact prefixLift 5970121
  have htrace : WordTrace (prefixWord ++ tailWord_5970121) baseStart_5970121 baseEnd_5970121 := by
    simpa [prefixWord, tailWord_5970121, baseEnd_5970121] using wordTrace_append hprefix tailTrace_5970121
  have hstable : (prefixWord ++ tailWord_5970121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5970121).length < 2 ^ (prefixWord ++ tailWord_5970121).sum := by decide
  have hdescent : baseEnd_5970121 < baseStart_5970121 := by decide
  rcases family_descends (prefixWord ++ tailWord_5970121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5970131 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 4, 5, 3]
def baseStart_5970131 : Nat := 118140960795 + 5970131 * 2 ^ 59
def prefixEnd_5970131 : Nat := 4983230072969 + 3 ^ 40 * 5970131 * 2
def baseEnd_5970131 : Nat := 3065546773307486568706373

theorem tailTrace_5970131 : CollatzResearch.WordTrace tailWord_5970131 prefixEnd_5970131 3065546773307486568706373 := by
  unfold tailWord_5970131
  simp only [CollatzResearch.WordTrace]
  refine ⟨217748566334242479044038247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145165710889494986029358831 217748566334242479044038247)
  ·
    refine ⟨326622849501363718566057371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217748566334242479044038247 326622849501363718566057371)
    ·
      refine ⟨489934274252045577849086057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326622849501363718566057371 489934274252045577849086057)
      ·
        refine ⟨367450705689034183386814543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 489934274252045577849086057 367450705689034183386814543)
        ·
          refine ⟨551176058533551275080221815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367450705689034183386814543 551176058533551275080221815)
          ·
            refine ⟨826764087800326912620332723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 551176058533551275080221815 826764087800326912620332723)
            ·
              refine ⟨1240146131700490368930499085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 826764087800326912620332723 1240146131700490368930499085)
              ·
                refine ⟨465054799387683888348937157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1240146131700490368930499085 465054799387683888348937157)
                ·
                  refine ⟨87197774885190729065425717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 465054799387683888348937157 87197774885190729065425717)
                  ·
                    refine ⟨8174791395486630849883661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 87197774885190729065425717 8174791395486630849883661)
                    ·
                      refine ⟨3065546773307486568706373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8174791395486630849883661 3065546773307486568706373)
                      ·
                        rfl

theorem cell23_5970131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 5, 3].length) (baseStart_5970131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5970131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5970131 prefixEnd_5970131 := by exact prefixLift 5970131
  have htrace : WordTrace (prefixWord ++ tailWord_5970131) baseStart_5970131 baseEnd_5970131 := by
    simpa [prefixWord, tailWord_5970131, baseEnd_5970131] using wordTrace_append hprefix tailTrace_5970131
  have hstable : (prefixWord ++ tailWord_5970131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5970131).length < 2 ^ (prefixWord ++ tailWord_5970131).sum := by decide
  have hdescent : baseEnd_5970131 < baseStart_5970131 := by decide
  rcases family_descends (prefixWord ++ tailWord_5970131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5970175 : List Nat := [1, 1, 2, 2, 1, 4, 3, 2, 2, 3, 2]
def baseStart_5970175 : Nat := 118140960795 + 5970175 * 2 ^ 59
def prefixEnd_5970175 : Nat := 4983230072969 + 3 ^ 40 * 5970175 * 2
def baseEnd_5970175 : Nat := 3065569366456284396556171

theorem tailTrace_5970175 : CollatzResearch.WordTrace tailWord_5970175 prefixEnd_5970175 3065569366456284396556171 := by
  unfold tailWord_5970175
  simp only [CollatzResearch.WordTrace]
  refine ⟨217750171146083074558639979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145166780764055383039093319 217750171146083074558639979)
  ·
    refine ⟨326625256719124611837959969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217750171146083074558639979 326625256719124611837959969)
    ·
      refine ⟨244968942539343458878469977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326625256719124611837959969 244968942539343458878469977)
      ·
        refine ⟨183726706904507594158852483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244968942539343458878469977 183726706904507594158852483)
        ·
          refine ⟨275590060356761391238278725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183726706904507594158852483 275590060356761391238278725)
          ·
            refine ⟨51673136316892760857177261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 275590060356761391238278725 51673136316892760857177261)
            ·
              refine ⟨19377426118834785321441473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51673136316892760857177261 19377426118834785321441473)
              ·
                refine ⟨14533069589126088991081105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19377426118834785321441473 14533069589126088991081105)
                ·
                  refine ⟨10899802191844566743310829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14533069589126088991081105 10899802191844566743310829)
                  ·
                    refine ⟨4087425821941712528741561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10899802191844566743310829 4087425821941712528741561)
                    ·
                      refine ⟨3065569366456284396556171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4087425821941712528741561 3065569366456284396556171)
                      ·
                        rfl

theorem cell23_5970175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 2, 2, 3, 2].length) (baseStart_5970175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5970175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5970175 prefixEnd_5970175 := by exact prefixLift 5970175
  have htrace : WordTrace (prefixWord ++ tailWord_5970175) baseStart_5970175 baseEnd_5970175 := by
    simpa [prefixWord, tailWord_5970175, baseEnd_5970175] using wordTrace_append hprefix tailTrace_5970175
  have hstable : (prefixWord ++ tailWord_5970175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5970175).length < 2 ^ (prefixWord ++ tailWord_5970175).sum := by decide
  have hdescent : baseEnd_5970175 < baseStart_5970175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5970175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5970181 : List Nat := [1, 3, 1, 1, 2, 1, 2, 1, 5, 6]
def baseStart_5970181 : Nat := 118140960795 + 5970181 * 2 ^ 59
def prefixEnd_5970181 : Nat := 4983230072969 + 3 ^ 40 * 5970181 * 2
def baseEnd_5970181 : Nat := 1021857482446737124360381

theorem tailTrace_5970181 : CollatzResearch.WordTrace tailWord_5970181 prefixEnd_5970181 1021857482446737124360381 := by
  unfold tailWord_5970181
  simp only [CollatzResearch.WordTrace]
  refine ⟨217750389984061337583358397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145166926656040891722238931 217750389984061337583358397)
  ·
    refine ⟨81656396244023001593759399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217750389984061337583358397 81656396244023001593759399)
    ·
      refine ⟨122484594366034502390639099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81656396244023001593759399 122484594366034502390639099)
      ·
        refine ⟨183726891549051753585958649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122484594366034502390639099 183726891549051753585958649)
        ·
          refine ⟨137795168661788815189468987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183726891549051753585958649 137795168661788815189468987)
          ·
            refine ⟨206692752992683222784203481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137795168661788815189468987 206692752992683222784203481)
            ·
              refine ⟨155019564744512417088152611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 206692752992683222784203481 155019564744512417088152611)
              ·
                refine ⟨232529347116768625632228917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155019564744512417088152611 232529347116768625632228917)
                ·
                  refine ⟨21799626292197058653021461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 232529347116768625632228917 21799626292197058653021461)
                  ·
                    refine ⟨1021857482446737124360381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21799626292197058653021461 1021857482446737124360381)
                    ·
                      rfl

theorem cell23_5970181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5, 6].length) (baseStart_5970181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5970181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5970181 prefixEnd_5970181 := by exact prefixLift 5970181
  have htrace : WordTrace (prefixWord ++ tailWord_5970181) baseStart_5970181 baseEnd_5970181 := by
    simpa [prefixWord, tailWord_5970181, baseEnd_5970181] using wordTrace_append hprefix tailTrace_5970181
  have hstable : (prefixWord ++ tailWord_5970181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5970181).length < 2 ^ (prefixWord ++ tailWord_5970181).sum := by decide
  have hdescent : baseEnd_5970181 < baseStart_5970181 := by decide
  rcases family_descends (prefixWord ++ tailWord_5970181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5970188 : List Nat := [2, 2, 1, 2, 2, 2, 2, 2, 3, 1, 4]
def baseStart_5970188 : Nat := 118140960795 + 5970188 * 2 ^ 59
def prefixEnd_5970188 : Nat := 4983230072969 + 3 ^ 40 * 5970188 * 2
def baseEnd_5970188 : Nat := 3065576041704792845693611

theorem tailTrace_5970188 : CollatzResearch.WordTrace tailWord_5970188 prefixEnd_5970188 3065576041704792845693611 := by
  unfold tailWord_5970188
  simp only [CollatzResearch.WordTrace]
  refine ⟨108875322647517988889431609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145167096863357318519242145 108875322647517988889431609)
  ·
    refine ⟨81656491985638491667073707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108875322647517988889431609 81656491985638491667073707)
    ·
      refine ⟨122484737978457737500610561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81656491985638491667073707 122484737978457737500610561)
      ·
        refine ⟨91863553483843303125457921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122484737978457737500610561 91863553483843303125457921)
        ·
          refine ⟨68897665112882477344093441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91863553483843303125457921 68897665112882477344093441)
          ·
            refine ⟨51673248834661858008070081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68897665112882477344093441 51673248834661858008070081)
            ·
              refine ⟨38754936625996393506052561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51673248834661858008070081 38754936625996393506052561)
              ·
                refine ⟨29066202469497295129539421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38754936625996393506052561 29066202469497295129539421)
                ·
                  refine ⟨10899825926061485673577283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29066202469497295129539421 10899825926061485673577283)
                  ·
                    refine ⟨16349738889092228510365925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10899825926061485673577283 16349738889092228510365925)
                    ·
                      refine ⟨3065576041704792845693611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16349738889092228510365925 3065576041704792845693611)
                      ·
                        rfl

theorem cell23_5970188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 3, 1, 4].length) (baseStart_5970188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5970188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5970188 prefixEnd_5970188 := by exact prefixLift 5970188
  have htrace : WordTrace (prefixWord ++ tailWord_5970188) baseStart_5970188 baseEnd_5970188 := by
    simpa [prefixWord, tailWord_5970188, baseEnd_5970188] using wordTrace_append hprefix tailTrace_5970188
  have hstable : (prefixWord ++ tailWord_5970188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5970188).length < 2 ^ (prefixWord ++ tailWord_5970188).sum := by decide
  have hdescent : baseEnd_5970188 < baseStart_5970188 := by decide
  rcases family_descends (prefixWord ++ tailWord_5970188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5970202 : List Nat := [3, 1, 1, 3, 4, 2, 1, 2, 1, 5]
def baseStart_5970202 : Nat := 118140960795 + 5970202 * 2 ^ 59
def prefixEnd_5970202 : Nat := 4983230072969 + 3 ^ 40 * 5970202 * 2
def baseEnd_5970202 : Nat := 1021861076811318596972849

theorem tailTrace_5970202 : CollatzResearch.WordTrace tailWord_5970202 prefixEnd_5970202 1021861076811318596972849 := by
  unfold tailWord_5970202
  simp only [CollatzResearch.WordTrace]
  refine ⟨54437788979246314542468215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145167437277990172113248573 54437788979246314542468215)
  ·
    refine ⟨81656683468869471813702323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54437788979246314542468215 81656683468869471813702323)
    ·
      refine ⟨122485025203304207720553485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81656683468869471813702323 122485025203304207720553485)
      ·
        refine ⟨45931884451239077895207557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122485025203304207720553485 45931884451239077895207557)
        ·
          refine ⟨8612228334607327105351417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45931884451239077895207557 8612228334607327105351417)
          ·
            refine ⟨6459171250955495329013563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8612228334607327105351417 6459171250955495329013563)
            ·
              refine ⟨9688756876433242993520345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6459171250955495329013563 9688756876433242993520345)
              ·
                refine ⟨7266567657324932245140259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9688756876433242993520345 7266567657324932245140259)
                ·
                  refine ⟨10899851485987398367710389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7266567657324932245140259 10899851485987398367710389)
                  ·
                    refine ⟨1021861076811318596972849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10899851485987398367710389 1021861076811318596972849)
                    ·
                      rfl

theorem cell23_5970202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 2, 1, 5].length) (baseStart_5970202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5970202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5970202 prefixEnd_5970202 := by exact prefixLift 5970202
  have htrace : WordTrace (prefixWord ++ tailWord_5970202) baseStart_5970202 baseEnd_5970202 := by
    simpa [prefixWord, tailWord_5970202, baseEnd_5970202] using wordTrace_append hprefix tailTrace_5970202
  have hstable : (prefixWord ++ tailWord_5970202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5970202).length < 2 ^ (prefixWord ++ tailWord_5970202).sum := by decide
  have hdescent : baseEnd_5970202 < baseStart_5970202 := by decide
  rcases family_descends (prefixWord ++ tailWord_5970202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5970211 : List Nat := [1, 1, 1, 4, 2, 2, 1, 11]
def baseStart_5970211 : Nat := 118140960795 + 5970211 * 2 ^ 59
def prefixEnd_5970211 : Nat := 4983230072969 + 3 ^ 40 * 5970211 * 2
def baseEnd_5970211 : Nat := 113540290805920231692815

theorem tailTrace_5970211 : CollatzResearch.WordTrace tailWord_5970211 prefixEnd_5970211 113540290805920231692815 := by
  unfold tailWord_5970211
  simp only [CollatzResearch.WordTrace]
  refine ⟨217751484173952652706950487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145167656115968435137966991 217751484173952652706950487)
  ·
    refine ⟨326627226260928979060425731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217751484173952652706950487 326627226260928979060425731)
    ·
      refine ⟨489940839391393468590638597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326627226260928979060425731 489940839391393468590638597)
      ·
        refine ⟨91863907385886275360744737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 489940839391393468590638597 91863907385886275360744737)
        ·
          refine ⟨68897930539414706520558553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91863907385886275360744737 68897930539414706520558553)
          ·
            refine ⟨51673447904561029890418915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68897930539414706520558553 51673447904561029890418915)
            ·
              refine ⟨77510171856841544835628373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51673447904561029890418915 77510171856841544835628373)
              ·
                refine ⟨113540290805920231692815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 77510171856841544835628373 113540290805920231692815)
                ·
                  rfl

theorem cell23_5970211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 11].length) (baseStart_5970211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5970211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5970211 prefixEnd_5970211 := by exact prefixLift 5970211
  have htrace : WordTrace (prefixWord ++ tailWord_5970211) baseStart_5970211 baseEnd_5970211 := by
    simpa [prefixWord, tailWord_5970211, baseEnd_5970211] using wordTrace_append hprefix tailTrace_5970211
  have hstable : (prefixWord ++ tailWord_5970211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5970211).length < 2 ^ (prefixWord ++ tailWord_5970211).sum := by decide
  have hdescent : baseEnd_5970211 < baseStart_5970211 := by decide
  rcases family_descends (prefixWord ++ tailWord_5970211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5970228 : List Nat := [2, 5, 1, 1, 1, 13]
def baseStart_5970228 : Nat := 118140960795 + 5970228 * 2 ^ 59
def prefixEnd_5970228 : Nat := 4983230072969 + 3 ^ 40 * 5970228 * 2
def baseEnd_5970228 : Nat := 12615623789839393782689

theorem tailTrace_5970228 : CollatzResearch.WordTrace tailWord_5970228 prefixEnd_5970228 12615623789839393782689 := by
  unfold tailWord_5970228
  simp only [CollatzResearch.WordTrace]
  refine ⟨108876052107445532305159669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145168069476594043073546225 108876052107445532305159669)
  ·
    refine ⟨10207129885073018653608719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108876052107445532305159669 10207129885073018653608719)
    ·
      refine ⟨15310694827609527980413079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10207129885073018653608719 15310694827609527980413079)
      ·
        refine ⟨22966042241414291970619619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15310694827609527980413079 22966042241414291970619619)
        ·
          refine ⟨34449063362121437955929429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22966042241414291970619619 34449063362121437955929429)
          ·
            refine ⟨12615623789839393782689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 34449063362121437955929429 12615623789839393782689)
            ·
              rfl

theorem cell23_5970228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 13].length) (baseStart_5970228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5970228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5970228 prefixEnd_5970228 := by exact prefixLift 5970228
  have htrace : WordTrace (prefixWord ++ tailWord_5970228) baseStart_5970228 baseEnd_5970228 := by
    simpa [prefixWord, tailWord_5970228, baseEnd_5970228] using wordTrace_append hprefix tailTrace_5970228
  have hstable : (prefixWord ++ tailWord_5970228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5970228).length < 2 ^ (prefixWord ++ tailWord_5970228).sum := by decide
  have hdescent : baseEnd_5970228 < baseStart_5970228 := by decide
  rcases family_descends (prefixWord ++ tailWord_5970228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5970239 : List Nat := [1, 1, 2, 2, 4, 1, 3, 4, 1, 2, 2]
def baseStart_5970239 : Nat := 118140960795 + 5970239 * 2 ^ 59
def prefixEnd_5970239 : Nat := 4983230072969 + 3 ^ 40 * 5970239 * 2
def baseEnd_5970239 : Nat := 3065602229218172146155877

theorem tailTrace_5970239 : CollatzResearch.WordTrace tailWord_5970239 prefixEnd_5970239 3065602229218172146155877 := by
  unfold tailWord_5970239
  simp only [CollatzResearch.WordTrace]
  refine ⟨217752505417851213488969771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145168336945234142325979847 217752505417851213488969771)
  ·
    refine ⟨326628758126776820233454657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217752505417851213488969771 326628758126776820233454657)
    ·
      refine ⟨244971568595082615175090993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326628758126776820233454657 244971568595082615175090993)
      ·
        refine ⟨183728676446311961381318245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244971568595082615175090993 183728676446311961381318245)
        ·
          refine ⟨34449126833683492758997171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 183728676446311961381318245 34449126833683492758997171)
          ·
            refine ⟨51673690250525239138495757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34449126833683492758997171 51673690250525239138495757)
            ·
              refine ⟨19377633843946964676935909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51673690250525239138495757 19377633843946964676935909)
              ·
                refine ⟨3633306345740055876925483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19377633843946964676935909 3633306345740055876925483)
                ·
                  refine ⟨5449959518610083815388225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3633306345740055876925483 5449959518610083815388225)
                  ·
                    refine ⟨4087469638957562861541169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5449959518610083815388225 4087469638957562861541169)
                    ·
                      refine ⟨3065602229218172146155877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4087469638957562861541169 3065602229218172146155877)
                      ·
                        rfl

theorem cell23_5970239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 4, 1, 2, 2].length) (baseStart_5970239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5970239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5970239 prefixEnd_5970239 := by exact prefixLift 5970239
  have htrace : WordTrace (prefixWord ++ tailWord_5970239) baseStart_5970239 baseEnd_5970239 := by
    simpa [prefixWord, tailWord_5970239, baseEnd_5970239] using wordTrace_append hprefix tailTrace_5970239
  have hstable : (prefixWord ++ tailWord_5970239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5970239).length < 2 ^ (prefixWord ++ tailWord_5970239).sum := by decide
  have hdescent : baseEnd_5970239 < baseStart_5970239 := by decide
  rcases family_descends (prefixWord ++ tailWord_5970239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5970270 : List Nat := [4, 4, 2, 1, 1, 2, 2, 1, 1, 5]
def baseStart_5970270 : Nat := 118140960795 + 5970270 * 2 ^ 59
def prefixEnd_5970270 : Nat := 4983230072969 + 3 ^ 40 * 5970270 * 2
def baseEnd_5970270 : Nat := 1021872715706153841622745

theorem tailTrace_5970270 : CollatzResearch.WordTrace tailWord_5970270 prefixEnd_5970270 1021872715706153841622745 := by
  unfold tailWord_5970270
  simp only [CollatzResearch.WordTrace]
  refine ⟨27219204510092363222918533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145169090720492603855565509 27219204510092363222918533)
  ·
    refine ⟨5103600845642318104297225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27219204510092363222918533 5103600845642318104297225)
    ·
      refine ⟨3827700634231738578222919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5103600845642318104297225 3827700634231738578222919)
      ·
        refine ⟨5741550951347607867334379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3827700634231738578222919 5741550951347607867334379)
        ·
          refine ⟨8612326427021411801001569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5741550951347607867334379 8612326427021411801001569)
          ·
            refine ⟨6459244820266058850751177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8612326427021411801001569 6459244820266058850751177)
            ·
              refine ⟨4844433615199544138063383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6459244820266058850751177 4844433615199544138063383)
              ·
                refine ⟨7266650422799316207095075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4844433615199544138063383 7266650422799316207095075)
                ·
                  refine ⟨10899975634198974310642613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7266650422799316207095075 10899975634198974310642613)
                  ·
                    refine ⟨1021872715706153841622745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10899975634198974310642613 1021872715706153841622745)
                    ·
                      rfl

theorem cell23_5970270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_5970270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5970270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5970270 prefixEnd_5970270 := by exact prefixLift 5970270
  have htrace : WordTrace (prefixWord ++ tailWord_5970270) baseStart_5970270 baseEnd_5970270 := by
    simpa [prefixWord, tailWord_5970270, baseEnd_5970270] using wordTrace_append hprefix tailTrace_5970270
  have hstable : (prefixWord ++ tailWord_5970270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5970270).length < 2 ^ (prefixWord ++ tailWord_5970270).sum := by decide
  have hdescent : baseEnd_5970270 < baseStart_5970270 := by decide
  rcases family_descends (prefixWord ++ tailWord_5970270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5970288 : List Nat := [2, 1, 1, 1, 4, 3, 1, 2, 2, 6]
def baseStart_5970288 : Nat := 118140960795 + 5970288 * 2 ^ 59
def prefixEnd_5970288 : Nat := 4983230072969 + 3 ^ 40 * 5970288 * 2
def baseEnd_5970288 : Nat := 1021875796590080818147717

theorem tailTrace_5970288 : CollatzResearch.WordTrace tailWord_5970288 prefixEnd_5970288 1021875796590080818147717 := by
  unfold tailWord_5970288
  simp only [CollatzResearch.WordTrace]
  refine ⟨108877146297336847428751759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145169528396449129905002345 108877146297336847428751759)
  ·
    refine ⟨163315719446005271143127639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108877146297336847428751759 163315719446005271143127639)
    ·
      refine ⟨244973579169007906714691459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163315719446005271143127639 244973579169007906714691459)
      ·
        refine ⟨367460368753511860072037189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244973579169007906714691459 367460368753511860072037189)
        ·
          refine ⟨68898819141283473763506973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 367460368753511860072037189 68898819141283473763506973)
          ·
            refine ⟨25837057177981302661315115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68898819141283473763506973 25837057177981302661315115)
            ·
              refine ⟨38755585766971953991972673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25837057177981302661315115 38755585766971953991972673)
              ·
                refine ⟨29066689325228965493979505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38755585766971953991972673 29066689325228965493979505)
                ·
                  refine ⟨21800016993921724120484629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29066689325228965493979505 21800016993921724120484629)
                  ·
                    refine ⟨1021875796590080818147717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21800016993921724120484629 1021875796590080818147717)
                    ·
                      rfl

theorem cell23_5970288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 2, 6].length) (baseStart_5970288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5970288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5970288 prefixEnd_5970288 := by exact prefixLift 5970288
  have htrace : WordTrace (prefixWord ++ tailWord_5970288) baseStart_5970288 baseEnd_5970288 := by
    simpa [prefixWord, tailWord_5970288, baseEnd_5970288] using wordTrace_append hprefix tailTrace_5970288
  have hstable : (prefixWord ++ tailWord_5970288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5970288).length < 2 ^ (prefixWord ++ tailWord_5970288).sum := by decide
  have hdescent : baseEnd_5970288 < baseStart_5970288 := by decide
  rcases family_descends (prefixWord ++ tailWord_5970288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5970305 : List Nat := [1, 2, 4, 3, 1, 1, 2, 1, 2, 6]
def baseStart_5970305 : Nat := 118140960795 + 5970305 * 2 ^ 59
def prefixEnd_5970305 : Nat := 4983230072969 + 3 ^ 40 * 5970305 * 2
def baseEnd_5970305 : Nat := 1021878706313789629310191

theorem tailTrace_5970305 : CollatzResearch.WordTrace tailWord_5970305 prefixEnd_5970305 1021878706313789629310191 := by
  unfold tailWord_5970305
  simp only [CollatzResearch.WordTrace]
  refine ⟨217754912635612106760872369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145169941757074737840581579 217754912635612106760872369)
  ·
    refine ⟨163316184476709080070654277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217754912635612106760872369 163316184476709080070654277)
    ·
      refine ⟨30621784589382952513247677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163316184476709080070654277 30621784589382952513247677)
      ·
        refine ⟨11483169221018607192467879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30621784589382952513247677 11483169221018607192467879)
        ·
          refine ⟨17224753831527910788701819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11483169221018607192467879 17224753831527910788701819)
          ·
            refine ⟨25837130747291866183052729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17224753831527910788701819 25837130747291866183052729)
            ·
              refine ⟨19377848060468899637289547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25837130747291866183052729 19377848060468899637289547)
              ·
                refine ⟨29066772090703349455934321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19377848060468899637289547 29066772090703349455934321)
                ·
                  refine ⟨21800079068027512091950741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29066772090703349455934321 21800079068027512091950741)
                  ·
                    refine ⟨1021878706313789629310191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21800079068027512091950741 1021878706313789629310191)
                    ·
                      rfl

theorem cell23_5970305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_5970305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5970305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5970305 prefixEnd_5970305 := by exact prefixLift 5970305
  have htrace : WordTrace (prefixWord ++ tailWord_5970305) baseStart_5970305 baseEnd_5970305 := by
    simpa [prefixWord, tailWord_5970305, baseEnd_5970305] using wordTrace_append hprefix tailTrace_5970305
  have hstable : (prefixWord ++ tailWord_5970305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5970305).length < 2 ^ (prefixWord ++ tailWord_5970305).sum := by decide
  have hdescent : baseEnd_5970305 < baseStart_5970305 := by decide
  rcases family_descends (prefixWord ++ tailWord_5970305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5970306 : List Nat := [3, 4, 2, 1, 2, 2, 1, 1, 1, 3, 3]
def baseStart_5970306 : Nat := 118140960795 + 5970306 * 2 ^ 59
def prefixEnd_5970306 : Nat := 4983230072969 + 3 ^ 40 * 5970306 * 2
def baseEnd_5970306 : Nat := 3065636632422023384018069

theorem tailTrace_5970306 : CollatzResearch.WordTrace tailWord_5970306 prefixEnd_5970306 3065636632422023384018069 := by
  unfold tailWord_5970306
  simp only [CollatzResearch.WordTrace]
  refine ⟨54438737277152120982914693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145169966072405655954439181 54438737277152120982914693)
  ·
    refine ⟨10207263239466022684296505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54438737277152120982914693 10207263239466022684296505)
    ·
      refine ⟨7655447429599517013222379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10207263239466022684296505 7655447429599517013222379)
      ·
        refine ⟨11483171144399275519833569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7655447429599517013222379 11483171144399275519833569)
        ·
          refine ⟨8612378358299456639875177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11483171144399275519833569 8612378358299456639875177)
          ·
            refine ⟨6459283768724592479906383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8612378358299456639875177 6459283768724592479906383)
            ·
              refine ⟨9688925653086888719859575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6459283768724592479906383 9688925653086888719859575)
              ·
                refine ⟨14533388479630333079789363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9688925653086888719859575 14533388479630333079789363)
                ·
                  refine ⟨21800082719445499619684045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14533388479630333079789363 21800082719445499619684045)
                  ·
                    refine ⟨8175031019792062357381517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21800082719445499619684045 8175031019792062357381517)
                    ·
                      refine ⟨3065636632422023384018069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8175031019792062357381517 3065636632422023384018069)
                      ·
                        rfl

theorem cell23_5970306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_5970306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5970306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5970306 prefixEnd_5970306 := by exact prefixLift 5970306
  have htrace : WordTrace (prefixWord ++ tailWord_5970306) baseStart_5970306 baseEnd_5970306 := by
    simpa [prefixWord, tailWord_5970306, baseEnd_5970306] using wordTrace_append hprefix tailTrace_5970306
  have hstable : (prefixWord ++ tailWord_5970306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5970306).length < 2 ^ (prefixWord ++ tailWord_5970306).sum := by decide
  have hdescent : baseEnd_5970306 < baseStart_5970306 := by decide
  rcases family_descends (prefixWord ++ tailWord_5970306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5970422 : List Nat := [5, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3]
def baseStart_5970422 : Nat := 118140960795 + 5970422 * 2 ^ 59
def prefixEnd_5970422 : Nat := 4983230072969 + 3 ^ 40 * 5970422 * 2
def baseEnd_5970422 : Nat := 3065696196177944930167535

theorem tailTrace_5970422 : CollatzResearch.WordTrace tailWord_5970422 prefixEnd_5970422 3065696196177944930167535 := by
  unfold tailWord_5970422
  simp only [CollatzResearch.WordTrace]
  refine ⟨13609948748511764733930095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145172786650792157161921013 13609948748511764733930095)
  ·
    refine ⟨20414923122767647100895143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13609948748511764733930095 20414923122767647100895143)
    ·
      refine ⟨30622384684151470651342715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20414923122767647100895143 30622384684151470651342715)
      ·
        refine ⟨45933577026227205977014073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30622384684151470651342715 45933577026227205977014073)
        ·
          refine ⟨34450182769670404482760555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45933577026227205977014073 34450182769670404482760555)
          ·
            refine ⟨51675274154505606724140833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34450182769670404482760555 51675274154505606724140833)
            ·
              refine ⟨38756455615879205043105625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51675274154505606724140833 38756455615879205043105625)
              ·
                refine ⟨29067341711909403782329219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38756455615879205043105625 29067341711909403782329219)
                ·
                  refine ⟨43601012567864105673493829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29067341711909403782329219 43601012567864105673493829)
                  ·
                    refine ⟨8175189856474519813780093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43601012567864105673493829 8175189856474519813780093)
                    ·
                      refine ⟨3065696196177944930167535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8175189856474519813780093 3065696196177944930167535)
                      ·
                        rfl

theorem cell23_5970422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_5970422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5970422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5970422 prefixEnd_5970422 := by exact prefixLift 5970422
  have htrace : WordTrace (prefixWord ++ tailWord_5970422) baseStart_5970422 baseEnd_5970422 := by
    simpa [prefixWord, tailWord_5970422, baseEnd_5970422] using wordTrace_append hprefix tailTrace_5970422
  have hstable : (prefixWord ++ tailWord_5970422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5970422).length < 2 ^ (prefixWord ++ tailWord_5970422).sum := by decide
  have hdescent : baseEnd_5970422 < baseStart_5970422 := by decide
  rcases family_descends (prefixWord ++ tailWord_5970422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5970425 : List Nat := [1, 2, 1, 3, 1, 2, 4, 3, 6]
def baseStart_5970425 : Nat := 118140960795 + 5970425 * 2 ^ 59
def prefixEnd_5970425 : Nat := 4983230072969 + 3 ^ 40 * 5970425 * 2
def baseEnd_5970425 : Nat := 340633081846656490936669

theorem tailTrace_5970425 : CollatzResearch.WordTrace tailWord_5970425 prefixEnd_5970425 340633081846656490936669 := by
  unfold tailWord_5970425
  simp only [CollatzResearch.WordTrace]
  refine ⟨217759289395177367255240729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145172859596784911503493819 217759289395177367255240729)
  ·
    refine ⟨163319467046383025441430547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217759289395177367255240729 163319467046383025441430547)
    ·
      refine ⟨244979200569574538162145821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163319467046383025441430547 244979200569574538162145821)
      ·
        refine ⟨91867200213590451810804683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 244979200569574538162145821 91867200213590451810804683)
        ·
          refine ⟨137800800320385677716207025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91867200213590451810804683 137800800320385677716207025)
          ·
            refine ⟨103350600240289258287155269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137800800320385677716207025 103350600240289258287155269)
            ·
              refine ⟨19378237545054235928841613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103350600240289258287155269 19378237545054235928841613)
              ·
                refine ⟨7266839079395338473315605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19378237545054235928841613 7266839079395338473315605)
                ·
                  refine ⟨340633081846656490936669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7266839079395338473315605 340633081846656490936669)
                  ·
                    rfl

theorem cell23_5970425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 3, 6].length) (baseStart_5970425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5970425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5970425 prefixEnd_5970425 := by exact prefixLift 5970425
  have htrace : WordTrace (prefixWord ++ tailWord_5970425) baseStart_5970425 baseEnd_5970425 := by
    simpa [prefixWord, tailWord_5970425, baseEnd_5970425] using wordTrace_append hprefix tailTrace_5970425
  have hstable : (prefixWord ++ tailWord_5970425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5970425).length < 2 ^ (prefixWord ++ tailWord_5970425).sum := by decide
  have hdescent : baseEnd_5970425 < baseStart_5970425 := by decide
  rcases family_descends (prefixWord ++ tailWord_5970425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5970446 : List Nat := [4, 1, 1, 2, 3, 2, 2, 3, 1, 4]
def baseStart_5970446 : Nat := 118140960795 + 5970446 * 2 ^ 59
def prefixEnd_5970446 : Nat := 4983230072969 + 3 ^ 40 * 5970446 * 2
def baseEnd_5970446 : Nat := 1021902839904550945422475

theorem tailTrace_5970446 : CollatzResearch.WordTrace tailWord_5970446 prefixEnd_5970446 1021902839904550945422475 := by
  unfold tailWord_5970446
  simp only [CollatzResearch.WordTrace]
  refine ⟨27220006916012660980219399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145173370218734191894503461 27220006916012660980219399)
  ·
    refine ⟨40830010374018991470329099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27220006916012660980219399 40830010374018991470329099)
    ·
      refine ⟨61245015561028487205493649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40830010374018991470329099 61245015561028487205493649)
      ·
        refine ⟨45933761670771365404120237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61245015561028487205493649 45933761670771365404120237)
        ·
          refine ⟨17225160626539262026545089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45933761670771365404120237 17225160626539262026545089)
          ·
            refine ⟨12918870469904446519908817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17225160626539262026545089 12918870469904446519908817)
            ·
              refine ⟨9689152852428334889931613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12918870469904446519908817 9689152852428334889931613)
              ·
                refine ⟨3633432319660625583724355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9689152852428334889931613 3633432319660625583724355)
                ·
                  refine ⟨5450148479490938375586533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3633432319660625583724355 5450148479490938375586533)
                  ·
                    refine ⟨1021902839904550945422475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5450148479490938375586533 1021902839904550945422475)
                    ·
                      rfl

theorem cell23_5970446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 3, 1, 4].length) (baseStart_5970446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5970446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5970446 prefixEnd_5970446 := by exact prefixLift 5970446
  have htrace : WordTrace (prefixWord ++ tailWord_5970446) baseStart_5970446 baseEnd_5970446 := by
    simpa [prefixWord, tailWord_5970446, baseEnd_5970446] using wordTrace_append hprefix tailTrace_5970446
  have hstable : (prefixWord ++ tailWord_5970446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5970446).length < 2 ^ (prefixWord ++ tailWord_5970446).sum := by decide
  have hdescent : baseEnd_5970446 < baseStart_5970446 := by decide
  rcases family_descends (prefixWord ++ tailWord_5970446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5970475 : List Nat := [1, 1, 1, 1, 2, 1, 3, 3, 5, 1, 4]
def baseStart_5970475 : Nat := 118140960795 + 5970475 * 2 ^ 59
def prefixEnd_5970475 : Nat := 4983230072969 + 3 ^ 40 * 5970475 * 2
def baseEnd_5970475 : Nat := 3065723410652633222804791

theorem tailTrace_5970475 : CollatzResearch.WordTrace tailWord_5970475 prefixEnd_5970475 3065723410652633222804791 := by
  unfold tailWord_5970475
  simp only [CollatzResearch.WordTrace]
  refine ⟨217761113044996225794560879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145174075363330817196373919 217761113044996225794560879)
  ·
    refine ⟨326641669567494338691841319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217761113044996225794560879 326641669567494338691841319)
    ·
      refine ⟨489962504351241508037761979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326641669567494338691841319 489962504351241508037761979)
      ·
        refine ⟨734943756526862262056642969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 489962504351241508037761979 734943756526862262056642969)
        ·
          refine ⟨551207817395146696542482227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 734943756526862262056642969 551207817395146696542482227)
          ·
            refine ⟨826811726092720044813723341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 551207817395146696542482227 826811726092720044813723341)
            ·
              refine ⟨310054397284770016805146253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 826811726092720044813723341 310054397284770016805146253)
              ·
                refine ⟨116270398981788756301929845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 310054397284770016805146253 116270398981788756301929845)
                ·
                  refine ⟨10900349904542695903305923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 116270398981788756301929845 10900349904542695903305923)
                  ·
                    refine ⟨16350524856814043854958885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10900349904542695903305923 16350524856814043854958885)
                    ·
                      refine ⟨3065723410652633222804791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16350524856814043854958885 3065723410652633222804791)
                      ·
                        rfl

theorem cell23_5970475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 5, 1, 4].length) (baseStart_5970475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5970475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5970475 prefixEnd_5970475 := by exact prefixLift 5970475
  have htrace : WordTrace (prefixWord ++ tailWord_5970475) baseStart_5970475 baseEnd_5970475 := by
    simpa [prefixWord, tailWord_5970475, baseEnd_5970475] using wordTrace_append hprefix tailTrace_5970475
  have hstable : (prefixWord ++ tailWord_5970475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5970475).length < 2 ^ (prefixWord ++ tailWord_5970475).sum := by decide
  have hdescent : baseEnd_5970475 < baseStart_5970475 := by decide
  rcases family_descends (prefixWord ++ tailWord_5970475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5970486 : List Nat := [5, 1, 2, 1, 2, 1, 2, 2, 3, 1, 3]
def baseStart_5970486 : Nat := 118140960795 + 5970486 * 2 ^ 59
def prefixEnd_5970486 : Nat := 4983230072969 + 3 ^ 40 * 5970486 * 2
def baseEnd_5970486 : Nat := 3065729058939832679767241

theorem tailTrace_5970486 : CollatzResearch.WordTrace tailWord_5970486 prefixEnd_5970486 3065729058939832679767241 := by
  unfold tailWord_5970486
  simp only [CollatzResearch.WordTrace]
  refine ⟨13610094640497273417075707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145174342831970916448807541 13610094640497273417075707)
  ·
    refine ⟨20415141960745910125613561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13610094640497273417075707 20415141960745910125613561)
    ·
      refine ⟨15311356470559432594210171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20415141960745910125613561 15311356470559432594210171)
      ·
        refine ⟨22967034705839148891315257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15311356470559432594210171 22967034705839148891315257)
        ·
          refine ⟨17225276029379361668486443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22967034705839148891315257 17225276029379361668486443)
          ·
            refine ⟨25837914044069042502729665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17225276029379361668486443 25837914044069042502729665)
            ·
              refine ⟨19378435533051781877047249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25837914044069042502729665 19378435533051781877047249)
              ·
                refine ⟨14533826649788836407785437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19378435533051781877047249 14533826649788836407785437)
                ·
                  refine ⟨5450184993670813652919539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14533826649788836407785437 5450184993670813652919539)
                  ·
                    refine ⟨8175277490506220479379309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5450184993670813652919539 8175277490506220479379309)
                    ·
                      refine ⟨3065729058939832679767241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8175277490506220479379309 3065729058939832679767241)
                      ·
                        rfl

theorem cell23_5970486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_5970486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5970486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5970486 prefixEnd_5970486 := by exact prefixLift 5970486
  have htrace : WordTrace (prefixWord ++ tailWord_5970486) baseStart_5970486 baseEnd_5970486 := by
    simpa [prefixWord, tailWord_5970486, baseEnd_5970486] using wordTrace_append hprefix tailTrace_5970486
  have hstable : (prefixWord ++ tailWord_5970486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5970486).length < 2 ^ (prefixWord ++ tailWord_5970486).sum := by decide
  have hdescent : baseEnd_5970486 < baseStart_5970486 := by decide
  rcases family_descends (prefixWord ++ tailWord_5970486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5970495 : List Nat := [1, 1, 2, 2, 3, 2, 1, 2, 3, 1, 5]
def baseStart_5970495 : Nat := 118140960795 + 5970495 * 2 ^ 59
def prefixEnd_5970495 : Nat := 4983230072969 + 3 ^ 40 * 5970495 * 2
def baseEnd_5970495 : Nat := 3065733680265723144554699

theorem tailTrace_5970495 : CollatzResearch.WordTrace tailWord_5970495 prefixEnd_5970495 3065733680265723144554699 := by
  unfold tailWord_5970495
  simp only [CollatzResearch.WordTrace]
  refine ⟨217761842504923769210288939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145174561669949179473525959 217761842504923769210288939)
  ·
    refine ⟨326642763757385653815433409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217761842504923769210288939 326642763757385653815433409)
    ·
      refine ⟨244982072818039240361575057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326642763757385653815433409 244982072818039240361575057)
      ·
        refine ⟨183736554613529430271181293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244982072818039240361575057 183736554613529430271181293)
        ·
          refine ⟨68901207980073536351692985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183736554613529430271181293 68901207980073536351692985)
          ·
            refine ⟨51675905985055152263769739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68901207980073536351692985 51675905985055152263769739)
            ·
              refine ⟨77513858977582728395654609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51675905985055152263769739 77513858977582728395654609)
              ·
                refine ⟨58135394233187046296740957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77513858977582728395654609 58135394233187046296740957)
                ·
                  refine ⟨21800772837445142361277859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58135394233187046296740957 21800772837445142361277859)
                  ·
                    refine ⟨32701159256167713541916789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21800772837445142361277859 32701159256167713541916789)
                    ·
                      refine ⟨3065733680265723144554699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32701159256167713541916789 3065733680265723144554699)
                      ·
                        rfl

theorem cell23_5970495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 3, 1, 5].length) (baseStart_5970495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5970495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5970495 prefixEnd_5970495 := by exact prefixLift 5970495
  have htrace : WordTrace (prefixWord ++ tailWord_5970495) baseStart_5970495 baseEnd_5970495 := by
    simpa [prefixWord, tailWord_5970495, baseEnd_5970495] using wordTrace_append hprefix tailTrace_5970495
  have hstable : (prefixWord ++ tailWord_5970495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5970495).length < 2 ^ (prefixWord ++ tailWord_5970495).sum := by decide
  have hdescent : baseEnd_5970495 < baseStart_5970495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5970495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5970503 : List Nat := [1, 1, 4, 1, 4, 3, 1, 3, 1, 1, 3]
def baseStart_5970503 : Nat := 118140960795 + 5970503 * 2 ^ 59
def prefixEnd_5970503 : Nat := 4983230072969 + 3 ^ 40 * 5970503 * 2
def baseEnd_5970503 : Nat := 3065737788110959113254663

theorem tailTrace_5970503 : CollatzResearch.WordTrace tailWord_5970503 prefixEnd_5970503 3065737788110959113254663 := by
  unfold tailWord_5970503
  simp only [CollatzResearch.WordTrace]
  refine ⟨217762134288894786576580163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145174756192596524384386775 217762134288894786576580163)
  ·
    refine ⟨326643201433342179864870245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217762134288894786576580163 326643201433342179864870245)
    ·
      refine ⟨61245600268751658724663171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 326643201433342179864870245 61245600268751658724663171)
      ·
        refine ⟨91868400403127488086994757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61245600268751658724663171 91868400403127488086994757)
        ·
          refine ⟨17225325075586404016311517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91868400403127488086994757 17225325075586404016311517)
          ·
            refine ⟨6459496903344901506116819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17225325075586404016311517 6459496903344901506116819)
            ·
              refine ⟨9689245355017352259175229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6459496903344901506116819 9689245355017352259175229)
              ·
                refine ⟨3633467008131507097190711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9689245355017352259175229 3633467008131507097190711)
                ·
                  refine ⟨5450200512197260645786067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3633467008131507097190711 5450200512197260645786067)
                  ·
                    refine ⟨8175300768295890968679101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5450200512197260645786067 8175300768295890968679101)
                    ·
                      refine ⟨3065737788110959113254663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8175300768295890968679101 3065737788110959113254663)
                      ·
                        rfl

theorem cell23_5970503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 3, 1, 1, 3].length) (baseStart_5970503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5970503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5970503 prefixEnd_5970503 := by exact prefixLift 5970503
  have htrace : WordTrace (prefixWord ++ tailWord_5970503) baseStart_5970503 baseEnd_5970503 := by
    simpa [prefixWord, tailWord_5970503, baseEnd_5970503] using wordTrace_append hprefix tailTrace_5970503
  have hstable : (prefixWord ++ tailWord_5970503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5970503).length < 2 ^ (prefixWord ++ tailWord_5970503).sum := by decide
  have hdescent : baseEnd_5970503 < baseStart_5970503 := by decide
  rcases family_descends (prefixWord ++ tailWord_5970503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5970535 : List Nat := [1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 6]
def baseStart_5970535 : Nat := 118140960795 + 5970535 * 2 ^ 59
def prefixEnd_5970535 : Nat := 4983230072969 + 3 ^ 40 * 5970535 * 2
def baseEnd_5970535 : Nat := 3065754219491902988054515

theorem tailTrace_5970535 : CollatzResearch.WordTrace tailWord_5970535 prefixEnd_5970535 3065754219491902988054515 := by
  unfold tailWord_5970535
  simp only [CollatzResearch.WordTrace]
  refine ⟨217763301424778856041745059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145175534283185904027830039 217763301424778856041745059)
  ·
    refine ⟨326644952137168284062617589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217763301424778856041745059 326644952137168284062617589)
    ·
      refine ⟨30622964262859526630870399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 326644952137168284062617589 30622964262859526630870399)
      ·
        refine ⟨45934446394289289946305599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30622964262859526630870399 45934446394289289946305599)
        ·
          refine ⟨68901669591433934919458399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45934446394289289946305599 68901669591433934919458399)
          ·
            refine ⟨103352504387150902379187599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68901669591433934919458399 103352504387150902379187599)
            ·
              refine ⟨155028756580726353568781399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103352504387150902379187599 155028756580726353568781399)
              ·
                refine ⟨232543134871089530353172099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155028756580726353568781399 232543134871089530353172099)
                ·
                  refine ⟨348814702306634295529758149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 232543134871089530353172099 348814702306634295529758149)
                  ·
                    refine ⟨65402756682493930411829653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 348814702306634295529758149 65402756682493930411829653)
                    ·
                      refine ⟨3065754219491902988054515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65402756682493930411829653 3065754219491902988054515)
                      ·
                        rfl

theorem cell23_5970535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_5970535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5970535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5970535 prefixEnd_5970535 := by exact prefixLift 5970535
  have htrace : WordTrace (prefixWord ++ tailWord_5970535) baseStart_5970535 baseEnd_5970535 := by
    simpa [prefixWord, tailWord_5970535, baseEnd_5970535] using wordTrace_append hprefix tailTrace_5970535
  have hstable : (prefixWord ++ tailWord_5970535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5970535).length < 2 ^ (prefixWord ++ tailWord_5970535).sum := by decide
  have hdescent : baseEnd_5970535 < baseStart_5970535 := by decide
  rcases family_descends (prefixWord ++ tailWord_5970535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5970536 : List Nat := [2, 1, 4, 3, 2, 1, 1, 3, 2, 4]
def baseStart_5970536 : Nat := 118140960795 + 5970536 * 2 ^ 59
def prefixEnd_5970536 : Nat := 4983230072969 + 3 ^ 40 * 5970536 * 2
def baseEnd_5970536 : Nat := 1021918244324185828047337

theorem tailTrace_5970536 : CollatzResearch.WordTrace tailWord_5970536 prefixEnd_5970536 1021918244324185828047337 := by
  unfold tailWord_5970536
  simp only [CollatzResearch.WordTrace]
  refine ⟨108881668948887616606265731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145175558598516822141687641 108881668948887616606265731)
  ·
    refine ⟨163322503423331424909398597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108881668948887616606265731 163322503423331424909398597)
    ·
      refine ⟨30622969391874642170512237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163322503423331424909398597 30622969391874642170512237)
      ·
        refine ⟨11483613521952990813942089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30622969391874642170512237 11483613521952990813942089)
        ·
          refine ⟨8612710141464743110456567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11483613521952990813942089 8612710141464743110456567)
          ·
            refine ⟨12919065212197114665684851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8612710141464743110456567 12919065212197114665684851)
            ·
              refine ⟨19378597818295671998527277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12919065212197114665684851 19378597818295671998527277)
              ·
                refine ⟨7266974181860876999447729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19378597818295671998527277 7266974181860876999447729)
                ·
                  refine ⟨5450230636395657749585797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7266974181860876999447729 5450230636395657749585797)
                  ·
                    refine ⟨1021918244324185828047337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5450230636395657749585797 1021918244324185828047337)
                    ·
                      rfl

theorem cell23_5970536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_5970536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5970536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5970536 prefixEnd_5970536 := by exact prefixLift 5970536
  have htrace : WordTrace (prefixWord ++ tailWord_5970536) baseStart_5970536 baseEnd_5970536 := by
    simpa [prefixWord, tailWord_5970536, baseEnd_5970536] using wordTrace_append hprefix tailTrace_5970536
  have hstable : (prefixWord ++ tailWord_5970536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5970536).length < 2 ^ (prefixWord ++ tailWord_5970536).sum := by decide
  have hdescent : baseEnd_5970536 < baseStart_5970536 := by decide
  rcases family_descends (prefixWord ++ tailWord_5970536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5970552 : List Nat := [2, 1, 2, 1, 1, 1, 2, 2, 2, 7, 2]
def baseStart_5970552 : Nat := 118140960795 + 5970552 * 2 ^ 59
def prefixEnd_5970552 : Nat := 4983230072969 + 3 ^ 40 * 5970552 * 2
def baseEnd_5970552 : Nat := 3065762948663029421541937

theorem tailTrace_5970552 : CollatzResearch.WordTrace tailWord_5970552 prefixEnd_5970552 3065762948663029421541937 := by
  unfold tailWord_5970552
  simp only [CollatzResearch.WordTrace]
  refine ⟨108881960732858633972556955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145175947643811511963409273 108881960732858633972556955)
  ·
    refine ⟨163322941099287950958835433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108881960732858633972556955 163322941099287950958835433)
    ·
      refine ⟨122492205824465963219126575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163322941099287950958835433 122492205824465963219126575)
      ·
        refine ⟨183738308736698944828689863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122492205824465963219126575 183738308736698944828689863)
        ·
          refine ⟨275607463105048417243034795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183738308736698944828689863 275607463105048417243034795)
          ·
            refine ⟨413411194657572625864552193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275607463105048417243034795 413411194657572625864552193)
            ·
              refine ⟨310058395993179469398414145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 413411194657572625864552193 310058395993179469398414145)
              ·
                refine ⟨232543796994884602048810609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 310058395993179469398414145 232543796994884602048810609)
                ·
                  refine ⟨174407847746163451536607957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 232543796994884602048810609 174407847746163451536607957)
                  ·
                    refine ⟨4087683931550705895389249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 174407847746163451536607957 4087683931550705895389249)
                    ·
                      refine ⟨3065762948663029421541937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4087683931550705895389249 3065762948663029421541937)
                      ·
                        rfl

theorem cell23_5970552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 2, 7, 2].length) (baseStart_5970552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5970552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5970552 prefixEnd_5970552 := by exact prefixLift 5970552
  have htrace : WordTrace (prefixWord ++ tailWord_5970552) baseStart_5970552 baseEnd_5970552 := by
    simpa [prefixWord, tailWord_5970552, baseEnd_5970552] using wordTrace_append hprefix tailTrace_5970552
  have hstable : (prefixWord ++ tailWord_5970552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5970552).length < 2 ^ (prefixWord ++ tailWord_5970552).sum := by decide
  have hdescent : baseEnd_5970552 < baseStart_5970552 := by decide
  rcases family_descends (prefixWord ++ tailWord_5970552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5970555 : List Nat := [1, 1, 1, 1, 1, 4, 2, 3, 2, 2, 5]
def baseStart_5970555 : Nat := 118140960795 + 5970555 * 2 ^ 59
def prefixEnd_5970555 : Nat := 4983230072969 + 3 ^ 40 * 5970555 * 2
def baseEnd_5970555 : Nat := 3065764489104992909804423

theorem tailTrace_5970555 : CollatzResearch.WordTrace tailWord_5970555 prefixEnd_5970555 3065764489104992909804423 := by
  unfold tailWord_5970555
  simp only [CollatzResearch.WordTrace]
  refine ⟨217764030884706399457473119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145176020589804266304982079 217764030884706399457473119)
  ·
    refine ⟨326646046327059599186209679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217764030884706399457473119 326646046327059599186209679)
    ·
      refine ⟨489969069490589398779314519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326646046327059599186209679 489969069490589398779314519)
      ·
        refine ⟨734953604235884098168971779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 489969069490589398779314519 734953604235884098168971779)
        ·
          refine ⟨1102430406353826147253457669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 734953604235884098168971779 1102430406353826147253457669)
          ·
            refine ⟨206705701191342402610023313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1102430406353826147253457669 206705701191342402610023313)
            ·
              refine ⟨155029275893506801957517485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 206705701191342402610023313 155029275893506801957517485)
              ·
                refine ⟨58135978460065050734069057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 155029275893506801957517485 58135978460065050734069057)
                ·
                  refine ⟨43601983845048788050551793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58135978460065050734069057 43601983845048788050551793)
                  ·
                    refine ⟨32701487883786591037913845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43601983845048788050551793 32701487883786591037913845)
                    ·
                      refine ⟨3065764489104992909804423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32701487883786591037913845 3065764489104992909804423)
                      ·
                        rfl

theorem cell23_5970555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 2, 5].length) (baseStart_5970555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5970555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5970555 prefixEnd_5970555 := by exact prefixLift 5970555
  have htrace : WordTrace (prefixWord ++ tailWord_5970555) baseStart_5970555 baseEnd_5970555 := by
    simpa [prefixWord, tailWord_5970555, baseEnd_5970555] using wordTrace_append hprefix tailTrace_5970555
  have hstable : (prefixWord ++ tailWord_5970555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5970555).length < 2 ^ (prefixWord ++ tailWord_5970555).sum := by decide
  have hdescent : baseEnd_5970555 < baseStart_5970555 := by decide
  rcases family_descends (prefixWord ++ tailWord_5970555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5970575 : List Nat := [1, 1, 2, 1, 1, 1, 1, 5, 4, 6]
def baseStart_5970575 : Nat := 118140960795 + 5970575 * 2 ^ 59
def prefixEnd_5970575 : Nat := 4983230072969 + 3 ^ 40 * 5970575 * 2
def baseEnd_5970575 : Nat := 1021924919572694277184777

theorem tailTrace_5970575 : CollatzResearch.WordTrace tailWord_5970575 prefixEnd_5970575 1021924919572694277184777 := by
  unfold tailWord_5970575
  simp only [CollatzResearch.WordTrace]
  refine ⟨217764760344633942873201179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145176506896422628582134119 217764760344633942873201179)
  ·
    refine ⟨326647140516950914309801769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217764760344633942873201179 326647140516950914309801769)
    ·
      refine ⟨244985355387713185732351327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326647140516950914309801769 244985355387713185732351327)
      ·
        refine ⟨367478033081569778598526991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244985355387713185732351327 367478033081569778598526991)
        ·
          refine ⟨551217049622354667897790487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367478033081569778598526991 551217049622354667897790487)
          ·
            refine ⟨826825574433532001846685731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 551217049622354667897790487 826825574433532001846685731)
            ·
              refine ⟨1240238361650298002770028597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 826825574433532001846685731 1240238361650298002770028597)
              ·
                refine ⟨116272346404715437759690181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1240238361650298002770028597 116272346404715437759690181)
                ·
                  refine ⟨21801064950884144579941909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 116272346404715437759690181 21801064950884144579941909)
                  ·
                    refine ⟨1021924919572694277184777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21801064950884144579941909 1021924919572694277184777)
                    ·
                      rfl

theorem cell23_5970575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4, 6].length) (baseStart_5970575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5970575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5970575 prefixEnd_5970575 := by exact prefixLift 5970575
  have htrace : WordTrace (prefixWord ++ tailWord_5970575) baseStart_5970575 baseEnd_5970575 := by
    simpa [prefixWord, tailWord_5970575, baseEnd_5970575] using wordTrace_append hprefix tailTrace_5970575
  have hstable : (prefixWord ++ tailWord_5970575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5970575).length < 2 ^ (prefixWord ++ tailWord_5970575).sum := by decide
  have hdescent : baseEnd_5970575 < baseStart_5970575 := by decide
  rcases family_descends (prefixWord ++ tailWord_5970575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5970622 : List Nat := [4, 2, 1, 1, 2, 1, 1, 2, 9]
def baseStart_5970622 : Nat := 118140960795 + 5970622 * 2 ^ 59
def prefixEnd_5970622 : Nat := 4983230072969 + 3 ^ 40 * 5970622 * 2
def baseEnd_5970622 : Nat := 340644321367649349740735

theorem tailTrace_5970622 : CollatzResearch.WordTrace tailWord_5970622 prefixEnd_5970622 340644321367649349740735 := by
  unfold tailWord_5970622
  simp only [CollatzResearch.WordTrace]
  refine ⟨27220809321932958737520265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145177649716975779933441413 27220809321932958737520265)
  ·
    refine ⟨20415606991449719053140199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27220809321932958737520265 20415606991449719053140199)
    ·
      refine ⟨30623410487174578579710299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20415606991449719053140199 30623410487174578579710299)
      ·
        refine ⟨45935115730761867869565449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30623410487174578579710299 45935115730761867869565449)
        ·
          refine ⟨34451336798071400902174087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45935115730761867869565449 34451336798071400902174087)
          ·
            refine ⟨51677005197107101353261131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34451336798071400902174087 51677005197107101353261131)
            ·
              refine ⟨77515507795660652029891697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51677005197107101353261131 77515507795660652029891697)
              ·
                refine ⟨58136630846745489022418773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77515507795660652029891697 58136630846745489022418773)
                ·
                  refine ⟨340644321367649349740735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 58136630846745489022418773 340644321367649349740735)
                  ·
                    rfl

theorem cell23_5970622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 9].length) (baseStart_5970622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5970622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5970622 prefixEnd_5970622 := by exact prefixLift 5970622
  have htrace : WordTrace (prefixWord ++ tailWord_5970622) baseStart_5970622 baseEnd_5970622 := by
    simpa [prefixWord, tailWord_5970622, baseEnd_5970622] using wordTrace_append hprefix tailTrace_5970622
  have hstable : (prefixWord ++ tailWord_5970622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5970622).length < 2 ^ (prefixWord ++ tailWord_5970622).sum := by decide
  have hdescent : baseEnd_5970622 < baseStart_5970622 := by decide
  rcases family_descends (prefixWord ++ tailWord_5970622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5970669 : List Nat := [1, 5, 1, 2, 1, 1, 2, 3, 2, 5]
def baseStart_5970669 : Nat := 118140960795 + 5970669 * 2 ^ 59
def prefixEnd_5970669 : Nat := 4983230072969 + 3 ^ 40 * 5970669 * 2
def baseEnd_5970669 : Nat := 1021941008633201821259633

theorem tailTrace_5970669 : CollatzResearch.WordTrace tailWord_5970669 prefixEnd_5970669 1021941008633201821259633 := by
  unfold tailWord_5970669
  simp only [CollatzResearch.WordTrace]
  refine ⟨217768188806293396927123061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145178792537528931284748707 217768188806293396927123061)
  ·
    refine ⟨20415767700590005961917787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 217768188806293396927123061 20415767700590005961917787)
    ·
      refine ⟨30623651550885008942876681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20415767700590005961917787 30623651550885008942876681)
      ·
        refine ⟨22967738663163756707157511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30623651550885008942876681 22967738663163756707157511)
        ·
          refine ⟨34451607994745635060736267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22967738663163756707157511 34451607994745635060736267)
          ·
            refine ⟨51677411992118452591104401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34451607994745635060736267 51677411992118452591104401)
            ·
              refine ⟨38758058994088839443328301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51677411992118452591104401 38758058994088839443328301)
              ·
                refine ⟨14534272122783314791248113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38758058994088839443328301 14534272122783314791248113)
                ·
                  refine ⟨10900704092087486093436085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14534272122783314791248113 10900704092087486093436085)
                  ·
                    refine ⟨1021941008633201821259633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10900704092087486093436085 1021941008633201821259633)
                    ·
                      rfl

theorem cell23_5970669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_5970669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5970669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5970669 prefixEnd_5970669 := by exact prefixLift 5970669
  have htrace : WordTrace (prefixWord ++ tailWord_5970669) baseStart_5970669 baseEnd_5970669 := by
    simpa [prefixWord, tailWord_5970669, baseEnd_5970669] using wordTrace_append hprefix tailTrace_5970669
  have hstable : (prefixWord ++ tailWord_5970669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5970669).length < 2 ^ (prefixWord ++ tailWord_5970669).sum := by decide
  have hdescent : baseEnd_5970669 < baseStart_5970669 := by decide
  rcases family_descends (prefixWord ++ tailWord_5970669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5970672 : List Nat := [2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 4]
def baseStart_5970672 : Nat := 118140960795 + 5970672 * 2 ^ 59
def prefixEnd_5970672 : Nat := 4983230072969 + 3 ^ 40 * 5970672 * 2
def baseEnd_5970672 : Nat := 3065824566341568952041385

theorem tailTrace_5970672 : CollatzResearch.WordTrace tailWord_5970672 prefixEnd_5970672 3065824566341568952041385 := by
  unfold tailWord_5970672
  simp only [CollatzResearch.WordTrace]
  refine ⟨108884149112641264219741135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145178865483521685626321513 108884149112641264219741135)
  ·
    refine ⟨163326223668961896329611703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108884149112641264219741135 163326223668961896329611703)
    ·
      refine ⟨244989335503442844494417555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163326223668961896329611703 244989335503442844494417555)
      ·
        refine ⟨367484003255164266741626333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244989335503442844494417555 367484003255164266741626333)
        ·
          refine ⟨137806501220686600028109875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 367484003255164266741626333 137806501220686600028109875)
          ·
            refine ⟨206709751831029900042164813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137806501220686600028109875 206709751831029900042164813)
            ·
              refine ⟨77516156936636212515811805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 206709751831029900042164813 77516156936636212515811805)
              ·
                refine ⟨29068558851238579693429427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77516156936636212515811805 29068558851238579693429427)
                ·
                  refine ⟨43602838276857869540144141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29068558851238579693429427 43602838276857869540144141)
                  ·
                    refine ⟨16351064353821701077554053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43602838276857869540144141 16351064353821701077554053)
                    ·
                      refine ⟨3065824566341568952041385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16351064353821701077554053 3065824566341568952041385)
                      ·
                        rfl

theorem cell23_5970672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 4].length) (baseStart_5970672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5970672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5970672 prefixEnd_5970672 := by exact prefixLift 5970672
  have htrace : WordTrace (prefixWord ++ tailWord_5970672) baseStart_5970672 baseEnd_5970672 := by
    simpa [prefixWord, tailWord_5970672, baseEnd_5970672] using wordTrace_append hprefix tailTrace_5970672
  have hstable : (prefixWord ++ tailWord_5970672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5970672).length < 2 ^ (prefixWord ++ tailWord_5970672).sum := by decide
  have hdescent : baseEnd_5970672 < baseStart_5970672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5970672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5970686 : List Nat := [4, 2, 2, 1, 2, 2, 1, 2, 2, 5]
def baseStart_5970686 : Nat := 118140960795 + 5970686 * 2 ^ 59
def prefixEnd_5970686 : Nat := 4983230072969 + 3 ^ 40 * 5970686 * 2
def baseEnd_5970686 : Nat := 1021943918356910632422107

theorem tailTrace_5970686 : CollatzResearch.WordTrace tailWord_5970686 prefixEnd_5970686 1021943918356910632422107 := by
  unfold tailWord_5970686
  simp only [CollatzResearch.WordTrace]
  refine ⟨27221101105903976103811489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145179205898154539220327941 27221101105903976103811489)
  ·
    refine ⟨20415825829427982077858617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27221101105903976103811489 20415825829427982077858617)
    ·
      refine ⟨15311869372070986558393963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20415825829427982077858617 15311869372070986558393963)
      ·
        refine ⟨22967804058106479837590945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15311869372070986558393963 22967804058106479837590945)
        ·
          refine ⟨17225853043579859878193209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22967804058106479837590945 17225853043579859878193209)
          ·
            refine ⟨12919389782684894908644907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17225853043579859878193209 12919389782684894908644907)
            ·
              refine ⟨19379084674027342362967361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12919389782684894908644907 19379084674027342362967361)
              ·
                refine ⟨14534313505520506772225521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19379084674027342362967361 14534313505520506772225521)
                ·
                  refine ⟨10900735129140380079169141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14534313505520506772225521 10900735129140380079169141)
                  ·
                    refine ⟨1021943918356910632422107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10900735129140380079169141 1021943918356910632422107)
                    ·
                      rfl

theorem cell23_5970686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_5970686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5970686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5970686 prefixEnd_5970686 := by exact prefixLift 5970686
  have htrace : WordTrace (prefixWord ++ tailWord_5970686) baseStart_5970686 baseEnd_5970686 := by
    simpa [prefixWord, tailWord_5970686, baseEnd_5970686] using wordTrace_append hprefix tailTrace_5970686
  have hstable : (prefixWord ++ tailWord_5970686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5970686).length < 2 ^ (prefixWord ++ tailWord_5970686).sum := by decide
  have hdescent : baseEnd_5970686 < baseStart_5970686 := by decide
  rcases family_descends (prefixWord ++ tailWord_5970686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5970709 : List Nat := [1, 3, 2, 1, 2, 2, 1, 2, 4, 2, 3]
def baseStart_5970709 : Nat := 118140960795 + 5970709 * 2 ^ 59
def prefixEnd_5970709 : Nat := 4983230072969 + 3 ^ 40 * 5970709 * 2
def baseEnd_5970709 : Nat := 3065843565125785307278715

theorem tailTrace_5970709 : CollatzResearch.WordTrace tailWord_5970709 prefixEnd_5970709 3065843565125785307278715 := by
  unfold tailWord_5970709
  simp only [CollatzResearch.WordTrace]
  refine ⟨217769647726148483758579181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145179765150765655839052787 217769647726148483758579181)
  ·
    refine ⟨81663617897305681409467193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217769647726148483758579181 81663617897305681409467193)
    ·
      refine ⟨61247713422979261057100395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81663617897305681409467193 61247713422979261057100395)
      ·
        refine ⟨91871570134468891585650593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61247713422979261057100395 91871570134468891585650593)
        ·
          refine ⟨68903677600851668689237945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91871570134468891585650593 68903677600851668689237945)
          ·
            refine ⟨51677758200638751516928459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68903677600851668689237945 51677758200638751516928459)
            ·
              refine ⟨77516637300958127275392689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51677758200638751516928459 77516637300958127275392689)
              ·
                refine ⟨58137477975718595456544517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77516637300958127275392689 58137477975718595456544517)
                ·
                  refine ⟨10900777120447236648102097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58137477975718595456544517 10900777120447236648102097)
                  ·
                    refine ⟨8175582840335427486076573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10900777120447236648102097 8175582840335427486076573)
                    ·
                      refine ⟨3065843565125785307278715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8175582840335427486076573 3065843565125785307278715)
                      ·
                        rfl

theorem cell23_5970709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 4, 2, 3].length) (baseStart_5970709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5970709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5970709 prefixEnd_5970709 := by exact prefixLift 5970709
  have htrace : WordTrace (prefixWord ++ tailWord_5970709) baseStart_5970709 baseEnd_5970709 := by
    simpa [prefixWord, tailWord_5970709, baseEnd_5970709] using wordTrace_append hprefix tailTrace_5970709
  have hstable : (prefixWord ++ tailWord_5970709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5970709).length < 2 ^ (prefixWord ++ tailWord_5970709).sum := by decide
  have hdescent : baseEnd_5970709 < baseStart_5970709 := by decide
  rcases family_descends (prefixWord ++ tailWord_5970709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5970746 : List Nat := [3, 1, 1, 1, 6, 1, 2, 2, 6]
def baseStart_5970746 : Nat := 118140960795 + 5970746 * 2 ^ 59
def prefixEnd_5970746 : Nat := 4983230072969 + 3 ^ 40 * 5970746 * 2
def baseEnd_5970746 : Nat := 340651395990000184724005

theorem tailTrace_5970746 : CollatzResearch.WordTrace tailWord_5970746 prefixEnd_5970746 340651395990000184724005 := by
  unfold tailWord_5970746
  simp only [CollatzResearch.WordTrace]
  refine ⟨54442749306753609769419023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145180664818009626051784061 54442749306753609769419023)
  ·
    refine ⟨81664123960130414654128535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54442749306753609769419023 81664123960130414654128535)
    ·
      refine ⟨122496185940195621981192803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81664123960130414654128535 122496185940195621981192803)
      ·
        refine ⟨183744278910293432971789205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122496185940195621981192803 183744278910293432971789205)
        ·
          refine ⟨8613013073920004670552619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 183744278910293432971789205 8613013073920004670552619)
          ·
            refine ⟨12919519610880007005828929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8613013073920004670552619 12919519610880007005828929)
            ·
              refine ⟨9689639708160005254371697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12919519610880007005828929 9689639708160005254371697)
              ·
                refine ⟨7267229781120003940778773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9689639708160005254371697 7267229781120003940778773)
                ·
                  refine ⟨340651395990000184724005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7267229781120003940778773 340651395990000184724005)
                  ·
                    rfl

theorem cell23_5970746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 2, 6].length) (baseStart_5970746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5970746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5970746 prefixEnd_5970746 := by exact prefixLift 5970746
  have htrace : WordTrace (prefixWord ++ tailWord_5970746) baseStart_5970746 baseEnd_5970746 := by
    simpa [prefixWord, tailWord_5970746, baseEnd_5970746] using wordTrace_append hprefix tailTrace_5970746
  have hstable : (prefixWord ++ tailWord_5970746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5970746).length < 2 ^ (prefixWord ++ tailWord_5970746).sum := by decide
  have hdescent : baseEnd_5970746 < baseStart_5970746 := by decide
  rcases family_descends (prefixWord ++ tailWord_5970746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5970750 : List Nat := [4, 2, 1, 2, 3, 1, 1, 4, 1, 4]
def baseStart_5970750 : Nat := 118140960795 + 5970750 * 2 ^ 59
def prefixEnd_5970750 : Nat := 4983230072969 + 3 ^ 40 * 5970750 * 2
def baseEnd_5970750 : Nat := 1021954872610873215622009

theorem tailTrace_5970750 : CollatzResearch.WordTrace tailWord_5970750 prefixEnd_5970750 1021954872610873215622009 := by
  unfold tailWord_5970750
  simp only [CollatzResearch.WordTrace]
  refine ⟨27221392889874993470102713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145180762079333298507214469 27221392889874993470102713)
  ·
    refine ⟨20416044667406245102577035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27221392889874993470102713 20416044667406245102577035)
    ·
      refine ⟨30624067001109367653865553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20416044667406245102577035 30624067001109367653865553)
      ·
        refine ⟨22968050250832025740399165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30624067001109367653865553 22968050250832025740399165)
        ·
          refine ⟨8613018844062009652649687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22968050250832025740399165 8613018844062009652649687)
          ·
            refine ⟨12919528266093014478974531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8613018844062009652649687 12919528266093014478974531)
            ·
              refine ⟨19379292399139521718461797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12919528266093014478974531 19379292399139521718461797)
              ·
                refine ⟨3633617324838660322211587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19379292399139521718461797 3633617324838660322211587)
                ·
                  refine ⟨5450425987257990483317381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3633617324838660322211587 5450425987257990483317381)
                  ·
                    refine ⟨1021954872610873215622009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5450425987257990483317381 1021954872610873215622009)
                    ·
                      rfl

theorem cell23_5970750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 4, 1, 4].length) (baseStart_5970750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5970750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5970750 prefixEnd_5970750 := by exact prefixLift 5970750
  have htrace : WordTrace (prefixWord ++ tailWord_5970750) baseStart_5970750 baseEnd_5970750 := by
    simpa [prefixWord, tailWord_5970750, baseEnd_5970750] using wordTrace_append hprefix tailTrace_5970750
  have hstable : (prefixWord ++ tailWord_5970750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5970750).length < 2 ^ (prefixWord ++ tailWord_5970750).sum := by decide
  have hdescent : baseEnd_5970750 < baseStart_5970750 := by decide
  rcases family_descends (prefixWord ++ tailWord_5970750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5970752 : List Nat := [2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 5]
def baseStart_5970752 : Nat := 118140960795 + 5970752 * 2 ^ 59
def prefixEnd_5970752 : Nat := 4983230072969 + 3 ^ 40 * 5970752 * 2
def baseEnd_5970752 : Nat := 3065865644793928639041017

theorem tailTrace_5970752 : CollatzResearch.WordTrace tailWord_5970752 prefixEnd_5970752 3065865644793928639041017 := by
  unfold tailWord_5970752
  simp only [CollatzResearch.WordTrace]
  refine ⟨108885608032496351051197255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145180810709995134734929673 108885608032496351051197255)
  ·
    refine ⟨163328412048744526576795883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108885608032496351051197255 163328412048744526576795883)
    ·
      refine ⟨244992618073116789865193825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163328412048744526576795883 244992618073116789865193825)
      ·
        refine ⟨183744463554837592398895369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244992618073116789865193825 183744463554837592398895369)
        ·
          refine ⟨137808347666128194299171527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183744463554837592398895369 137808347666128194299171527)
          ·
            refine ⟨206712521499192291448757291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137808347666128194299171527 206712521499192291448757291)
            ·
              refine ⟨310068782248788437173135937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206712521499192291448757291 310068782248788437173135937)
              ·
                refine ⟨232551586686591327879851953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 310068782248788437173135937 232551586686591327879851953)
                ·
                  refine ⟨174413690014943495909888965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 232551586686591327879851953 174413690014943495909888965)
                  ·
                    refine ⟨32702566877801905483104181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 174413690014943495909888965 32702566877801905483104181)
                    ·
                      refine ⟨3065865644793928639041017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32702566877801905483104181 3065865644793928639041017)
                      ·
                        rfl

theorem cell23_5970752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 5].length) (baseStart_5970752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5970752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5970752 prefixEnd_5970752 := by exact prefixLift 5970752
  have htrace : WordTrace (prefixWord ++ tailWord_5970752) baseStart_5970752 baseEnd_5970752 := by
    simpa [prefixWord, tailWord_5970752, baseEnd_5970752] using wordTrace_append hprefix tailTrace_5970752
  have hstable : (prefixWord ++ tailWord_5970752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5970752).length < 2 ^ (prefixWord ++ tailWord_5970752).sum := by decide
  have hdescent : baseEnd_5970752 < baseStart_5970752 := by decide
  rcases family_descends (prefixWord ++ tailWord_5970752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5970766 : List Nat := [4, 1, 1, 1, 1, 1, 1, 4, 4, 3, 2]
def baseStart_5970766 : Nat := 118140960795 + 5970766 * 2 ^ 59
def prefixEnd_5970766 : Nat := 4983230072969 + 3 ^ 40 * 5970766 * 2
def baseEnd_5970766 : Nat := 3065872833523091584265953

theorem tailTrace_5970766 : CollatzResearch.WordTrace tailWord_5970766 prefixEnd_5970766 3065872833523091584265953 := by
  unfold tailWord_5970766
  simp only [CollatzResearch.WordTrace]
  refine ⟨27221465835867747811675519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145181151124627988328936101 27221465835867747811675519)
  ·
    refine ⟨40832198753801621717513279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27221465835867747811675519 40832198753801621717513279)
    ·
      refine ⟨61248298130702432576269919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40832198753801621717513279 61248298130702432576269919)
      ·
        refine ⟨91872447196053648864404879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61248298130702432576269919 91872447196053648864404879)
        ·
          refine ⟨137808670794080473296607319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91872447196053648864404879 137808670794080473296607319)
          ·
            refine ⟨206713006191120709944910979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137808670794080473296607319 206713006191120709944910979)
            ·
              refine ⟨310069509286681064917366469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206713006191120709944910979 310069509286681064917366469)
              ·
                refine ⟨58138032991252699672006213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 310069509286681064917366469 58138032991252699672006213)
                ·
                  refine ⟨10900881185859881188501165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58138032991252699672006213 10900881185859881188501165)
                  ·
                    refine ⟨4087830444697455445687937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10900881185859881188501165 4087830444697455445687937)
                    ·
                      refine ⟨3065872833523091584265953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4087830444697455445687937 3065872833523091584265953)
                      ·
                        rfl

theorem cell23_5970766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 4, 3, 2].length) (baseStart_5970766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5970766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5970766 prefixEnd_5970766 := by exact prefixLift 5970766
  have htrace : WordTrace (prefixWord ++ tailWord_5970766) baseStart_5970766 baseEnd_5970766 := by
    simpa [prefixWord, tailWord_5970766, baseEnd_5970766] using wordTrace_append hprefix tailTrace_5970766
  have hstable : (prefixWord ++ tailWord_5970766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5970766).length < 2 ^ (prefixWord ++ tailWord_5970766).sum := by decide
  have hdescent : baseEnd_5970766 < baseStart_5970766 := by decide
  rcases family_descends (prefixWord ++ tailWord_5970766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5970789 : List Nat := [1, 3, 1, 3, 1, 1, 4, 2, 1, 6]
def baseStart_5970789 : Nat := 118140960795 + 5970789 * 2 ^ 59
def prefixEnd_5970789 : Nat := 4983230072969 + 3 ^ 40 * 5970789 * 2
def baseEnd_5970789 : Nat := 1021961547859381664759449

theorem tailTrace_5970789 : CollatzResearch.WordTrace tailWord_5970789 prefixEnd_5970789 1021961547859381664759449 := by
  unfold tailWord_5970789
  simp only [CollatzResearch.WordTrace]
  refine ⟨217772565565858657421491421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145181710377239104947660947 217772565565858657421491421)
  ·
    refine ⟨81664712087196996533059283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217772565565858657421491421 81664712087196996533059283)
    ·
      refine ⟨122497068130795494799588925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81664712087196996533059283 122497068130795494799588925)
      ·
        refine ⟨45936400549048310549845847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122497068130795494799588925 45936400549048310549845847)
        ·
          refine ⟨68904600823572465824768771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45936400549048310549845847 68904600823572465824768771)
          ·
            refine ⟨103356901235358698737153157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68904600823572465824768771 103356901235358698737153157)
            ·
              refine ⟨19379418981629756013216217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103356901235358698737153157 19379418981629756013216217)
              ·
                refine ⟨14534564236222317009912163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19379418981629756013216217 14534564236222317009912163)
                ·
                  refine ⟨21801846354333475514868245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14534564236222317009912163 21801846354333475514868245)
                  ·
                    refine ⟨1021961547859381664759449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21801846354333475514868245 1021961547859381664759449)
                    ·
                      rfl

theorem cell23_5970789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 2, 1, 6].length) (baseStart_5970789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5970789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5970789 prefixEnd_5970789 := by exact prefixLift 5970789
  have htrace : WordTrace (prefixWord ++ tailWord_5970789) baseStart_5970789 baseEnd_5970789 := by
    simpa [prefixWord, tailWord_5970789, baseEnd_5970789] using wordTrace_append hprefix tailTrace_5970789
  have hstable : (prefixWord ++ tailWord_5970789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5970789).length < 2 ^ (prefixWord ++ tailWord_5970789).sum := by decide
  have hdescent : baseEnd_5970789 < baseStart_5970789 := by decide
  rcases family_descends (prefixWord ++ tailWord_5970789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5970796 : List Nat := [2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 4]
def baseStart_5970796 : Nat := 118140960795 + 5970796 * 2 ^ 59
def prefixEnd_5970796 : Nat := 4983230072969 + 3 ^ 40 * 5970796 * 2
def baseEnd_5970796 : Nat := 3065888237942726466890815

theorem tailTrace_5970796 : CollatzResearch.WordTrace tailWord_5970796 prefixEnd_5970796 3065888237942726466890815 := by
  unfold tailWord_5970796
  simp only [CollatzResearch.WordTrace]
  refine ⟨108886410438416648808498121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145181880584555531744664161 108886410438416648808498121)
  ·
    refine ⟨81664807828812486606373591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108886410438416648808498121 81664807828812486606373591)
    ·
      refine ⟨122497211743218729909560387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81664807828812486606373591 122497211743218729909560387)
      ·
        refine ⟨183745817614828094864340581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122497211743218729909560387 183745817614828094864340581)
        ·
          refine ⟨34452340802780267787063859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 183745817614828094864340581 34452340802780267787063859)
          ·
            refine ⟨51678511204170401680595789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34452340802780267787063859 51678511204170401680595789)
            ·
              refine ⟨19379441701563900630223421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51678511204170401680595789 19379441701563900630223421)
              ·
                refine ⟨7267290638086462736333783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19379441701563900630223421 7267290638086462736333783)
                ·
                  refine ⟨10900935957129694104500675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7267290638086462736333783 10900935957129694104500675)
                  ·
                    refine ⟨16351403935694541156751013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10900935957129694104500675 16351403935694541156751013)
                    ·
                      refine ⟨3065888237942726466890815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16351403935694541156751013 3065888237942726466890815)
                      ·
                        rfl

theorem cell23_5970796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 4].length) (baseStart_5970796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5970796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5970796 prefixEnd_5970796 := by exact prefixLift 5970796
  have htrace : WordTrace (prefixWord ++ tailWord_5970796) baseStart_5970796 baseEnd_5970796 := by
    simpa [prefixWord, tailWord_5970796, baseEnd_5970796] using wordTrace_append hprefix tailTrace_5970796
  have hstable : (prefixWord ++ tailWord_5970796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5970796).length < 2 ^ (prefixWord ++ tailWord_5970796).sum := by decide
  have hdescent : baseEnd_5970796 < baseStart_5970796 := by decide
  rcases family_descends (prefixWord ++ tailWord_5970796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5970813 : List Nat := [1, 4, 1, 1, 2, 1, 3, 3, 3, 2, 2]
def baseStart_5970813 : Nat := 118140960795 + 5970813 * 2 ^ 59
def prefixEnd_5970813 : Nat := 4983230072969 + 3 ^ 40 * 5970813 * 2
def baseEnd_5970813 : Nat := 3065896967113852900378237

theorem tailTrace_5970813 : CollatzResearch.WordTrace tailWord_5970813 prefixEnd_5970813 3065896967113852900378237 := by
  unfold tailWord_5970813
  simp only [CollatzResearch.WordTrace]
  refine ⟨217773440917771709520365093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145182293945181139680243395 217773440917771709520365093)
  ·
    refine ⟨40832520172082195535068455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 217773440917771709520365093 40832520172082195535068455)
    ·
      refine ⟨61248780258123293302602683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40832520172082195535068455 61248780258123293302602683)
      ·
        refine ⟨91873170387184939953904025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61248780258123293302602683 91873170387184939953904025)
        ·
          refine ⟨68904877790388704965428019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91873170387184939953904025 68904877790388704965428019)
          ·
            refine ⟨103357316685583057448142029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68904877790388704965428019 103357316685583057448142029)
            ·
              refine ⟨38758993757093646543053261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103357316685583057448142029 38758993757093646543053261)
              ·
                refine ⟨14534622658910117453644973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38758993757093646543053261 14534622658910117453644973)
                ·
                  refine ⟨5450483497091294045116865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14534622658910117453644973 5450483497091294045116865)
                  ·
                    refine ⟨4087862622818470533837649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5450483497091294045116865 4087862622818470533837649)
                    ·
                      refine ⟨3065896967113852900378237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4087862622818470533837649 3065896967113852900378237)
                      ·
                        rfl

theorem cell23_5970813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3, 3, 2, 2].length) (baseStart_5970813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5970813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5970813 prefixEnd_5970813 := by exact prefixLift 5970813
  have htrace : WordTrace (prefixWord ++ tailWord_5970813) baseStart_5970813 baseEnd_5970813 := by
    simpa [prefixWord, tailWord_5970813, baseEnd_5970813] using wordTrace_append hprefix tailTrace_5970813
  have hstable : (prefixWord ++ tailWord_5970813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5970813).length < 2 ^ (prefixWord ++ tailWord_5970813).sum := by decide
  have hdescent : baseEnd_5970813 < baseStart_5970813 := by decide
  rcases family_descends (prefixWord ++ tailWord_5970813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5970826 : List Nat := [3, 1, 2, 4, 1, 2, 1, 1, 1, 1, 6]
def baseStart_5970826 : Nat := 118140960795 + 5970826 * 2 ^ 59
def prefixEnd_5970826 : Nat := 4983230072969 + 3 ^ 40 * 5970826 * 2
def baseEnd_5970826 : Nat := 3065903642362361349515677

theorem tailTrace_5970826 : CollatzResearch.WordTrace tailWord_5970826 prefixEnd_5970826 3065903642362361349515677 := by
  unfold tailWord_5970826
  simp only [CollatzResearch.WordTrace]
  refine ⟨54443478766681153185147083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145182610044483075160392221 54443478766681153185147083)
  ·
    refine ⟨81665218150021729777720625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54443478766681153185147083 81665218150021729777720625)
    ·
      refine ⟨61248913612516297333290469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81665218150021729777720625 61248913612516297333290469)
      ·
        refine ⟨11484171302346805749991963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61248913612516297333290469 11484171302346805749991963)
        ·
          refine ⟨17226256953520208624987945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11484171302346805749991963 17226256953520208624987945)
          ·
            refine ⟨12919692715140156468740959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17226256953520208624987945 12919692715140156468740959)
            ·
              refine ⟨19379539072710234703111439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12919692715140156468740959 19379539072710234703111439)
              ·
                refine ⟨29069308609065352054667159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19379539072710234703111439 29069308609065352054667159)
                ·
                  refine ⟨43603962913598028082000739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29069308609065352054667159 43603962913598028082000739)
                  ·
                    refine ⟨65405944370397042123001109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43603962913598028082000739 65405944370397042123001109)
                    ·
                      refine ⟨3065903642362361349515677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65405944370397042123001109 3065903642362361349515677)
                      ·
                        rfl

theorem cell23_5970826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_5970826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5970826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5970826 prefixEnd_5970826 := by exact prefixLift 5970826
  have htrace : WordTrace (prefixWord ++ tailWord_5970826) baseStart_5970826 baseEnd_5970826 := by
    simpa [prefixWord, tailWord_5970826, baseEnd_5970826] using wordTrace_append hprefix tailTrace_5970826
  have hstable : (prefixWord ++ tailWord_5970826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5970826).length < 2 ^ (prefixWord ++ tailWord_5970826).sum := by decide
  have hdescent : baseEnd_5970826 < baseStart_5970826 := by decide
  rcases family_descends (prefixWord ++ tailWord_5970826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5970847 : List Nat := [1, 1, 2, 5, 2, 1, 3, 3, 1, 2, 2]
def baseStart_5970847 : Nat := 118140960795 + 5970847 * 2 ^ 59
def prefixEnd_5970847 : Nat := 4983230072969 + 3 ^ 40 * 5970847 * 2
def baseEnd_5970847 : Nat := 3065914425456105767353081

theorem tailTrace_5970847 : CollatzResearch.WordTrace tailWord_5970847 prefixEnd_5970847 3065914425456105767353081 := by
  unfold tailWord_5970847
  simp only [CollatzResearch.WordTrace]
  refine ⟨217774680999648533327102795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145183120666432355551401863 217774680999648533327102795)
  ·
    refine ⟨326662021499472799990654193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217774680999648533327102795 326662021499472799990654193)
    ·
      refine ⟨244996516124604599992990645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326662021499472799990654193 244996516124604599992990645)
      ·
        refine ⟨22968423386681681249342873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 244996516124604599992990645 22968423386681681249342873)
        ·
          refine ⟨17226317540011260937007155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22968423386681681249342873 17226317540011260937007155)
          ·
            refine ⟨25839476310016891405510733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17226317540011260937007155 25839476310016891405510733)
            ·
              refine ⟨9689803616256334277066525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25839476310016891405510733 9689803616256334277066525)
              ·
                refine ⟨3633676356096125353899947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9689803616256334277066525 3633676356096125353899947)
                ·
                  refine ⟨5450514534144188030849921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3633676356096125353899947 5450514534144188030849921)
                  ·
                    refine ⟨4087885900608141023137441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5450514534144188030849921 4087885900608141023137441)
                    ·
                      refine ⟨3065914425456105767353081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4087885900608141023137441 3065914425456105767353081)
                      ·
                        rfl

theorem cell23_5970847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_5970847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5970847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5970847 prefixEnd_5970847 := by exact prefixLift 5970847
  have htrace : WordTrace (prefixWord ++ tailWord_5970847) baseStart_5970847 baseEnd_5970847 := by
    simpa [prefixWord, tailWord_5970847, baseEnd_5970847] using wordTrace_append hprefix tailTrace_5970847
  have hstable : (prefixWord ++ tailWord_5970847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5970847).length < 2 ^ (prefixWord ++ tailWord_5970847).sum := by decide
  have hdescent : baseEnd_5970847 < baseStart_5970847 := by decide
  rcases family_descends (prefixWord ++ tailWord_5970847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5970880 : List Nat := [2, 1, 1, 2, 3, 3, 4, 1, 2, 1, 3]
def baseStart_5970880 : Nat := 118140960795 + 5970880 * 2 ^ 59
def prefixEnd_5970880 : Nat := 4983230072969 + 3 ^ 40 * 5970880 * 2
def baseEnd_5970880 : Nat := 3065931370317704138240429

theorem tailTrace_5970880 : CollatzResearch.WordTrace tailWord_5970880 prefixEnd_5970880 3065931370317704138240429 := by
  unfold tailWord_5970880
  simp only [CollatzResearch.WordTrace]
  refine ⟨108887942304264489981527047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145183923072352653308702729 108887942304264489981527047)
  ·
    refine ⟨163331913456396734972290571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108887942304264489981527047 163331913456396734972290571)
    ·
      refine ⟨244997870184595102458435857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163331913456396734972290571 244997870184595102458435857)
      ·
        refine ⟨183748402638446326843826893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244997870184595102458435857 183748402638446326843826893)
        ·
          refine ⟨68905650989417372566435085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183748402638446326843826893 68905650989417372566435085)
          ·
            refine ⟨25839619121031514712413157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68905650989417372566435085 25839619121031514712413157)
            ·
              refine ⟨4844928585193409008577467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25839619121031514712413157 4844928585193409008577467)
              ·
                refine ⟨7267392877790113512866201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4844928585193409008577467 7267392877790113512866201)
                ·
                  refine ⟨5450544658342585134649651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7267392877790113512866201 5450544658342585134649651)
                  ·
                    refine ⟨8175816987513877701974477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5450544658342585134649651 8175816987513877701974477)
                    ·
                      refine ⟨3065931370317704138240429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8175816987513877701974477 3065931370317704138240429)
                      ·
                        rfl

theorem cell23_5970880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4, 1, 2, 1, 3].length) (baseStart_5970880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5970880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5970880 prefixEnd_5970880 := by exact prefixLift 5970880
  have htrace : WordTrace (prefixWord ++ tailWord_5970880) baseStart_5970880 baseEnd_5970880 := by
    simpa [prefixWord, tailWord_5970880, baseEnd_5970880] using wordTrace_append hprefix tailTrace_5970880
  have hstable : (prefixWord ++ tailWord_5970880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5970880).length < 2 ^ (prefixWord ++ tailWord_5970880).sum := by decide
  have hdescent : baseEnd_5970880 < baseStart_5970880 := by decide
  rcases family_descends (prefixWord ++ tailWord_5970880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5970884 : List Nat := [2, 3, 3, 3, 2, 1, 1, 2, 1, 2, 3]
def baseStart_5970884 : Nat := 118140960795 + 5970884 * 2 ^ 59
def prefixEnd_5970884 : Nat := 4983230072969 + 3 ^ 40 * 5970884 * 2
def baseEnd_5970884 : Nat := 3065933424240322122590411

theorem tailTrace_5970884 : CollatzResearch.WordTrace tailWord_5970884 prefixEnd_5970884 3065933424240322122590411 := by
  unfold tailWord_5970884
  simp only [CollatzResearch.WordTrace]
  refine ⟨108888015250257244323099853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145184020333676325764133137 108888015250257244323099853)
  ·
    refine ⟨40833005718846466621162445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108888015250257244323099853 40833005718846466621162445)
    ·
      refine ⟨15312377144567424982935917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40833005718846466621162445 15312377144567424982935917)
      ·
        refine ⟨5742141429212784368600969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15312377144567424982935917 5742141429212784368600969)
        ·
          refine ⟨4306606071909588276450727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5742141429212784368600969 4306606071909588276450727)
          ·
            refine ⟨6459909107864382414676091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4306606071909588276450727 6459909107864382414676091)
            ·
              refine ⟨9689863661796573622014137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6459909107864382414676091 9689863661796573622014137)
              ·
                refine ⟨7267397746347430216510603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9689863661796573622014137 7267397746347430216510603)
                ·
                  refine ⟨10901096619521145324765905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7267397746347430216510603 10901096619521145324765905)
                  ·
                    refine ⟨8175822464640858993574429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10901096619521145324765905 8175822464640858993574429)
                    ·
                      refine ⟨3065933424240322122590411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8175822464640858993574429 3065933424240322122590411)
                      ·
                        rfl

theorem cell23_5970884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_5970884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5970884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5970884 prefixEnd_5970884 := by exact prefixLift 5970884
  have htrace : WordTrace (prefixWord ++ tailWord_5970884) baseStart_5970884 baseEnd_5970884 := by
    simpa [prefixWord, tailWord_5970884, baseEnd_5970884] using wordTrace_append hprefix tailTrace_5970884
  have hstable : (prefixWord ++ tailWord_5970884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5970884).length < 2 ^ (prefixWord ++ tailWord_5970884).sum := by decide
  have hdescent : baseEnd_5970884 < baseStart_5970884 := by decide
  rcases family_descends (prefixWord ++ tailWord_5970884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5970903 : List Nat := [1, 1, 3, 2, 1, 1, 2, 4, 4, 2, 2]
def baseStart_5970903 : Nat := 118140960795 + 5970903 * 2 ^ 59
def prefixEnd_5970903 : Nat := 4983230072969 + 3 ^ 40 * 5970903 * 2
def baseEnd_5970903 : Nat := 3065943180372757548252823

theorem tailTrace_5970903 : CollatzResearch.WordTrace tailWord_5970903 prefixEnd_5970903 3065943180372757548252823 := by
  unfold tailWord_5970903
  simp only [CollatzResearch.WordTrace]
  refine ⟨217776723487445654891141363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145184482324963769927427575 217776723487445654891141363)
  ·
    refine ⟨326665085231168482336712045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217776723487445654891141363 326665085231168482336712045)
    ·
      refine ⟨122499406961688180876267017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 326665085231168482336712045 122499406961688180876267017)
      ·
        refine ⟨91874555221266135657200263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122499406961688180876267017 91874555221266135657200263)
        ·
          refine ⟨137811832831899203485800395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91874555221266135657200263 137811832831899203485800395)
          ·
            refine ⟨206717749247848805228700593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137811832831899203485800395 206717749247848805228700593)
            ·
              refine ⟨155038311935886603921525445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 206717749247848805228700593 155038311935886603921525445)
              ·
                refine ⟨29069683487978738235286021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 155038311935886603921525445 29069683487978738235286021)
                ·
                  refine ⟨5450565653996013419116129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29069683487978738235286021 5450565653996013419116129)
                  ·
                    refine ⟨4087924240497010064337097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5450565653996013419116129 4087924240497010064337097)
                    ·
                      refine ⟨3065943180372757548252823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4087924240497010064337097 3065943180372757548252823)
                      ·
                        rfl

theorem cell23_5970903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 4, 2, 2].length) (baseStart_5970903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5970903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5970903 prefixEnd_5970903 := by exact prefixLift 5970903
  have htrace : WordTrace (prefixWord ++ tailWord_5970903) baseStart_5970903 baseEnd_5970903 := by
    simpa [prefixWord, tailWord_5970903, baseEnd_5970903] using wordTrace_append hprefix tailTrace_5970903
  have hstable : (prefixWord ++ tailWord_5970903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5970903).length < 2 ^ (prefixWord ++ tailWord_5970903).sum := by decide
  have hdescent : baseEnd_5970903 < baseStart_5970903 := by decide
  rcases family_descends (prefixWord ++ tailWord_5970903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5970906 : List Nat := [3, 1, 1, 2, 4, 1, 2, 1, 2, 1, 5]
def baseStart_5970906 : Nat := 118140960795 + 5970906 * 2 ^ 59
def prefixEnd_5970906 : Nat := 4983230072969 + 3 ^ 40 * 5970906 * 2
def baseEnd_5970906 : Nat := 3065944720814721036515309

theorem tailTrace_5970906 : CollatzResearch.WordTrace tailWord_5970906 prefixEnd_5970906 3065944720814721036515309 := by
  unfold tailWord_5970906
  simp only [CollatzResearch.WordTrace]
  refine ⟨54444208226608696600875143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145184555270956524269000381 54444208226608696600875143)
  ·
    refine ⟨81666312339913044901312715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54444208226608696600875143 81666312339913044901312715)
    ·
      refine ⟨122499468509869567351969073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81666312339913044901312715 122499468509869567351969073)
      ·
        refine ⟨91874601382402175513976805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122499468509869567351969073 91874601382402175513976805)
        ·
          refine ⟨17226487759200407908870651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91874601382402175513976805 17226487759200407908870651)
          ·
            refine ⟨25839731638800611863305977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17226487759200407908870651 25839731638800611863305977)
            ·
              refine ⟨19379798729100458897479483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25839731638800611863305977 19379798729100458897479483)
              ·
                refine ⟨29069698093650688346219225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19379798729100458897479483 29069698093650688346219225)
                ·
                  refine ⟨21802273570238016259664419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29069698093650688346219225 21802273570238016259664419)
                  ·
                    refine ⟨32703410355357024389496629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21802273570238016259664419 32703410355357024389496629)
                    ·
                      refine ⟨3065944720814721036515309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32703410355357024389496629 3065944720814721036515309)
                      ·
                        rfl

theorem cell23_5970906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_5970906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5970906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5970906 prefixEnd_5970906 := by exact prefixLift 5970906
  have htrace : WordTrace (prefixWord ++ tailWord_5970906) baseStart_5970906 baseEnd_5970906 := by
    simpa [prefixWord, tailWord_5970906, baseEnd_5970906] using wordTrace_append hprefix tailTrace_5970906
  have hstable : (prefixWord ++ tailWord_5970906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5970906).length < 2 ^ (prefixWord ++ tailWord_5970906).sum := by decide
  have hdescent : baseEnd_5970906 < baseStart_5970906 := by decide
  rcases family_descends (prefixWord ++ tailWord_5970906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5970920 : List Nat := [2, 1, 4, 1, 1, 1, 3, 4, 2, 2, 2]
def baseStart_5970920 : Nat := 118140960795 + 5970920 * 2 ^ 59
def prefixEnd_5970920 : Nat := 4983230072969 + 3 ^ 40 * 5970920 * 2
def baseEnd_5970920 : Nat := 3065951909543883981740245

theorem tailTrace_5970920 : CollatzResearch.WordTrace tailWord_5970920 prefixEnd_5970920 3065951909543883981740245 := by
  unfold tailWord_5970920
  simp only [CollatzResearch.WordTrace]
  refine ⟨108888671764192033397255107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145184895685589377863006809 108888671764192033397255107)
  ·
    refine ⟨163333007646288050095882661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108888671764192033397255107 163333007646288050095882661)
    ·
      refine ⟨30624938933679009392977999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163333007646288050095882661 30624938933679009392977999)
      ·
        refine ⟨45937408400518514089466999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30624938933679009392977999 45937408400518514089466999)
        ·
          refine ⟨68906112600777771134200499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45937408400518514089466999 68906112600777771134200499)
          ·
            refine ⟨103359168901166656701300749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68906112600777771134200499 103359168901166656701300749)
            ·
              refine ⟨38759688337937496262987781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103359168901166656701300749 38759688337937496262987781)
              ·
                refine ⟨7267441563363280549310209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38759688337937496262987781 7267441563363280549310209)
                ·
                  refine ⟨5450581172522460411982657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7267441563363280549310209 5450581172522460411982657)
                  ·
                    refine ⟨4087935879391845308986993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5450581172522460411982657 4087935879391845308986993)
                    ·
                      refine ⟨3065951909543883981740245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4087935879391845308986993 3065951909543883981740245)
                      ·
                        rfl

theorem cell23_5970920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 4, 2, 2, 2].length) (baseStart_5970920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5970920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5970920 prefixEnd_5970920 := by exact prefixLift 5970920
  have htrace : WordTrace (prefixWord ++ tailWord_5970920) baseStart_5970920 baseEnd_5970920 := by
    simpa [prefixWord, tailWord_5970920, baseEnd_5970920] using wordTrace_append hprefix tailTrace_5970920
  have hstable : (prefixWord ++ tailWord_5970920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5970920).length < 2 ^ (prefixWord ++ tailWord_5970920).sum := by decide
  have hdescent : baseEnd_5970920 < baseStart_5970920 := by decide
  rcases family_descends (prefixWord ++ tailWord_5970920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5970939 : List Nat := [1, 1, 1, 1, 1, 3, 3, 4, 1, 7]
def baseStart_5970939 : Nat := 118140960795 + 5970939 * 2 ^ 59
def prefixEnd_5970939 : Nat := 4983230072969 + 3 ^ 40 * 5970939 * 2
def baseEnd_5970939 : Nat := 1021987221892106469134219

theorem tailTrace_5970939 : CollatzResearch.WordTrace tailWord_5970939 prefixEnd_5970939 1021987221892106469134219 := by
  unfold tailWord_5970939
  simp only [CollatzResearch.WordTrace]
  refine ⟨217778036515315233039451871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145185357676876822026301247 217778036515315233039451871)
  ·
    refine ⟨326667054772972849559177807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217778036515315233039451871 326667054772972849559177807)
    ·
      refine ⟨490000582159459274338766711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326667054772972849559177807 490000582159459274338766711)
      ·
        refine ⟨735000873239188911508150067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 490000582159459274338766711 735000873239188911508150067)
        ·
          refine ⟨1102501309858783367262225101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 735000873239188911508150067 1102501309858783367262225101)
          ·
            refine ⟨413437991197043762723334413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1102501309858783367262225101 413437991197043762723334413)
            ·
              refine ⟨155039246698891411021250405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 413437991197043762723334413 155039246698891411021250405)
              ·
                refine ⟨29069858756042139566484451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 155039246698891411021250405 29069858756042139566484451)
                ·
                  refine ⟨43604788134063209349726677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29069858756042139566484451 43604788134063209349726677)
                  ·
                    refine ⟨1021987221892106469134219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43604788134063209349726677 1021987221892106469134219)
                    ·
                      rfl

theorem cell23_5970939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 7].length) (baseStart_5970939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5970939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5970939 prefixEnd_5970939 := by exact prefixLift 5970939
  have htrace : WordTrace (prefixWord ++ tailWord_5970939) baseStart_5970939 baseEnd_5970939 := by
    simpa [prefixWord, tailWord_5970939, baseEnd_5970939] using wordTrace_append hprefix tailTrace_5970939
  have hstable : (prefixWord ++ tailWord_5970939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5970939).length < 2 ^ (prefixWord ++ tailWord_5970939).sum := by decide
  have hdescent : baseEnd_5970939 < baseStart_5970939 := by decide
  rcases family_descends (prefixWord ++ tailWord_5970939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5970956 : List Nat := [2, 2, 1, 2, 3, 3, 1, 1, 1, 7]
def baseStart_5970956 : Nat := 118140960795 + 5970956 * 2 ^ 59
def prefixEnd_5970956 : Nat := 4983230072969 + 3 ^ 40 * 5970956 * 2
def baseEnd_5970956 : Nat := 1021990131615815280296693

theorem tailTrace_5970956 : CollatzResearch.WordTrace tailWord_5970956 prefixEnd_5970956 1021990131615815280296693 := by
  unfold tailWord_5970956
  simp only [CollatzResearch.WordTrace]
  refine ⟨108889328278126822471410361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145185771037502429961880481 108889328278126822471410361)
  ·
    refine ⟨81666996208595116853557771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108889328278126822471410361 81666996208595116853557771)
    ·
      refine ⟨122500494312892675280336657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81666996208595116853557771 122500494312892675280336657)
      ·
        refine ⟨91875370734669506460252493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122500494312892675280336657 91875370734669506460252493)
        ·
          refine ⟨34453264025501064922594685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91875370734669506460252493 34453264025501064922594685)
          ·
            refine ⟨12919974009562899345973007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34453264025501064922594685 12919974009562899345973007)
            ·
              refine ⟨19379961014344349018959511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12919974009562899345973007 19379961014344349018959511)
              ·
                refine ⟨29069941521516523528439267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19379961014344349018959511 29069941521516523528439267)
                ·
                  refine ⟨43604912282274785292658901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29069941521516523528439267 43604912282274785292658901)
                  ·
                    refine ⟨1021990131615815280296693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43604912282274785292658901 1021990131615815280296693)
                    ·
                      rfl

theorem cell23_5970956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 1, 7].length) (baseStart_5970956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5970956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5970956 prefixEnd_5970956 := by exact prefixLift 5970956
  have htrace : WordTrace (prefixWord ++ tailWord_5970956) baseStart_5970956 baseEnd_5970956 := by
    simpa [prefixWord, tailWord_5970956, baseEnd_5970956] using wordTrace_append hprefix tailTrace_5970956
  have hstable : (prefixWord ++ tailWord_5970956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5970956).length < 2 ^ (prefixWord ++ tailWord_5970956).sum := by decide
  have hdescent : baseEnd_5970956 < baseStart_5970956 := by decide
  rcases family_descends (prefixWord ++ tailWord_5970956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5970993 : List Nat := [1, 2, 2, 3, 1, 2, 1, 3, 2, 4, 2]
def baseStart_5970993 : Nat := 118140960795 + 5970993 * 2 ^ 59
def prefixEnd_5970993 : Nat := 4983230072969 + 3 ^ 40 * 5970993 * 2
def baseEnd_5970993 : Nat := 3065989393631662196127409

theorem tailTrace_5970993 : CollatzResearch.WordTrace tailWord_5970993 prefixEnd_5970993 3065989393631662196127409 := by
  unfold tailWord_5970993
  simp only [CollatzResearch.WordTrace]
  refine ⟨217780006057119600261917633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145186670704746400174611755 217780006057119600261917633)
  ·
    refine ⟨163335004542839700196438225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217780006057119600261917633 163335004542839700196438225)
    ·
      refine ⟨122501253407129775147328669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163335004542839700196438225 122501253407129775147328669)
      ·
        refine ⟨45937970027673665680248251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122501253407129775147328669 45937970027673665680248251)
        ·
          refine ⟨68906955041510498520372377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45937970027673665680248251 68906955041510498520372377)
          ·
            refine ⟨51680216281132873890279283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68906955041510498520372377 51680216281132873890279283)
            ·
              refine ⟨77520324421699310835418925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51680216281132873890279283 77520324421699310835418925)
              ·
                refine ⟨29070121658137241563282097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77520324421699310835418925 29070121658137241563282097)
                ·
                  refine ⟨21802591243602931172461573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29070121658137241563282097 21802591243602931172461573)
                  ·
                    refine ⟨4087985858175549594836545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21802591243602931172461573 4087985858175549594836545)
                    ·
                      refine ⟨3065989393631662196127409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4087985858175549594836545 3065989393631662196127409)
                      ·
                        rfl

theorem cell23_5970993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 2, 4, 2].length) (baseStart_5970993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5970993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5970993 prefixEnd_5970993 := by exact prefixLift 5970993
  have htrace : WordTrace (prefixWord ++ tailWord_5970993) baseStart_5970993 baseEnd_5970993 := by
    simpa [prefixWord, tailWord_5970993, baseEnd_5970993] using wordTrace_append hprefix tailTrace_5970993
  have hstable : (prefixWord ++ tailWord_5970993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5970993).length < 2 ^ (prefixWord ++ tailWord_5970993).sum := by decide
  have hdescent : baseEnd_5970993 < baseStart_5970993 := by decide
  rcases family_descends (prefixWord ++ tailWord_5970993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5971050 : List Nat := [3, 1, 3, 2, 2, 1, 4, 1, 6]
def baseStart_5971050 : Nat := 118140960795 + 5971050 * 2 ^ 59
def prefixEnd_5971050 : Nat := 4983230072969 + 3 ^ 40 * 5971050 * 2
def baseEnd_5971050 : Nat := 340668740225440941457183

theorem tailTrace_5971050 : CollatzResearch.WordTrace tailWord_5971050 prefixEnd_5971050 340668740225440941457183 := by
  unfold tailWord_5971050
  simp only [CollatzResearch.WordTrace]
  refine ⟨54445521254478274749185651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145188056678608732664495069 54445521254478274749185651)
  ·
    refine ⟨81668281881717412123778477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54445521254478274749185651 81668281881717412123778477)
    ·
      refine ⟨30625605705644029546416929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81668281881717412123778477 30625605705644029546416929)
      ·
        refine ⟨22969204279233022159812697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30625605705644029546416929 22969204279233022159812697)
        ·
          refine ⟨17226903209424766619859523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22969204279233022159812697 17226903209424766619859523)
          ·
            refine ⟨25840354814137149929789285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17226903209424766619859523 25840354814137149929789285)
            ·
              refine ⟨4845066527650715611835491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25840354814137149929789285 4845066527650715611835491)
              ·
                refine ⟨7267599791476073417753237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4845066527650715611835491 7267599791476073417753237)
                ·
                  refine ⟨340668740225440941457183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7267599791476073417753237 340668740225440941457183)
                  ·
                    rfl

theorem cell23_5971050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4, 1, 6].length) (baseStart_5971050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5971050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5971050 prefixEnd_5971050 := by exact prefixLift 5971050
  have htrace : WordTrace (prefixWord ++ tailWord_5971050) baseStart_5971050 baseEnd_5971050 := by
    simpa [prefixWord, tailWord_5971050, baseEnd_5971050] using wordTrace_append hprefix tailTrace_5971050
  have hstable : (prefixWord ++ tailWord_5971050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5971050).length < 2 ^ (prefixWord ++ tailWord_5971050).sum := by decide
  have hdescent : baseEnd_5971050 < baseStart_5971050 := by decide
  rcases family_descends (prefixWord ++ tailWord_5971050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5971083 : List Nat := [1, 1, 1, 1, 4, 1, 1, 7, 1, 1, 4]
def baseStart_5971083 : Nat := 118140960795 + 5971083 * 2 ^ 59
def prefixEnd_5971083 : Nat := 4983230072969 + 3 ^ 40 * 5971083 * 2
def baseEnd_5971083 : Nat := 3066035606890566844001995

theorem tailTrace_5971083 : CollatzResearch.WordTrace tailWord_5971083 prefixEnd_5971083 3066035606890566844001995 := by
  unfold tailWord_5971083
  simp only [CollatzResearch.WordTrace]
  refine ⟨217783288626793545632693903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145188859084529030421795935 217783288626793545632693903)
  ·
    refine ⟨326674932940190318449040855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217783288626793545632693903 326674932940190318449040855)
    ·
      refine ⟨490012399410285477673561283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326674932940190318449040855 490012399410285477673561283)
      ·
        refine ⟨735018599115428216510341925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 490012399410285477673561283 735018599115428216510341925)
        ·
          refine ⟨137815987334142790595689111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 735018599115428216510341925 137815987334142790595689111)
          ·
            refine ⟨206723981001214185893533667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137815987334142790595689111 206723981001214185893533667)
            ·
              refine ⟨310085971501821278840300501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206723981001214185893533667 310085971501821278840300501)
              ·
                refine ⟨7267639957073936222819543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 310085971501821278840300501 7267639957073936222819543)
                ·
                  refine ⟨10901459935610904334229315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7267639957073936222819543 10901459935610904334229315)
                  ·
                    refine ⟨16352189903416356501343973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10901459935610904334229315 16352189903416356501343973)
                    ·
                      refine ⟨3066035606890566844001995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16352189903416356501343973 3066035606890566844001995)
                      ·
                        rfl

theorem cell23_5971083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 7, 1, 1, 4].length) (baseStart_5971083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5971083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5971083 prefixEnd_5971083 := by exact prefixLift 5971083
  have htrace : WordTrace (prefixWord ++ tailWord_5971083) baseStart_5971083 baseEnd_5971083 := by
    simpa [prefixWord, tailWord_5971083, baseEnd_5971083] using wordTrace_append hprefix tailTrace_5971083
  have hstable : (prefixWord ++ tailWord_5971083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5971083).length < 2 ^ (prefixWord ++ tailWord_5971083).sum := by decide
  have hdescent : baseEnd_5971083 < baseStart_5971083 := by decide
  rcases family_descends (prefixWord ++ tailWord_5971083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5971134 : List Nat := [4, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4]
def baseStart_5971134 : Nat := 118140960795 + 5971134 * 2 ^ 59
def prefixEnd_5971134 : Nat := 4983230072969 + 3 ^ 40 * 5971134 * 2
def baseEnd_5971134 : Nat := 3066061794403946144464261

theorem tailTrace_5971134 : CollatzResearch.WordTrace tailWord_5971134 prefixEnd_5971134 3066061794403946144464261 := by
  unfold tailWord_5971134
  simp only [CollatzResearch.WordTrace]
  refine ⟨27223143593701097667850057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145190099166405854228533637 27223143593701097667850057)
  ·
    refine ⟨20417357695275823250887543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27223143593701097667850057 20417357695275823250887543)
    ·
      refine ⟨30626036542913734876331315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20417357695275823250887543 30626036542913734876331315)
      ·
        refine ⟨45939054814370602314496973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30626036542913734876331315 45939054814370602314496973)
        ·
          refine ⟨17227145555388975867936365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45939054814370602314496973 17227145555388975867936365)
          ·
            refine ⟨6460179583270865950476137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17227145555388975867936365 6460179583270865950476137)
            ·
              refine ⟨4845134687453149462857103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6460179583270865950476137 4845134687453149462857103)
              ·
                refine ⟨7267702031179724194285655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4845134687453149462857103 7267702031179724194285655)
                ·
                  refine ⟨10901553046769586291428483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7267702031179724194285655 10901553046769586291428483)
                  ·
                    refine ⟨16352329570154379437142725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10901553046769586291428483 16352329570154379437142725)
                    ·
                      refine ⟨3066061794403946144464261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16352329570154379437142725 3066061794403946144464261)
                      ·
                        rfl

theorem cell23_5971134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4].length) (baseStart_5971134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5971134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5971134 prefixEnd_5971134 := by exact prefixLift 5971134
  have htrace : WordTrace (prefixWord ++ tailWord_5971134) baseStart_5971134 baseEnd_5971134 := by
    simpa [prefixWord, tailWord_5971134, baseEnd_5971134] using wordTrace_append hprefix tailTrace_5971134
  have hstable : (prefixWord ++ tailWord_5971134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5971134).length < 2 ^ (prefixWord ++ tailWord_5971134).sum := by decide
  have hdescent : baseEnd_5971134 < baseStart_5971134 := by decide
  rcases family_descends (prefixWord ++ tailWord_5971134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5971193 : List Nat := [1, 2, 1, 3, 1, 1, 5, 1, 2, 1, 5]
def baseStart_5971193 : Nat := 118140960795 + 5971193 * 2 ^ 59
def prefixEnd_5971193 : Nat := 4983230072969 + 3 ^ 40 * 5971193 * 2
def baseEnd_5971193 : Nat := 3066092089762561413626489

theorem tailTrace_5971193 : CollatzResearch.WordTrace tailWord_5971193 prefixEnd_5971193 3066092089762561413626489 := by
  unfold tailWord_5971193
  simp only [CollatzResearch.WordTrace]
  refine ⟨217787300656395034419198233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145191533770930022946132155 217787300656395034419198233)
  ·
    refine ⟨163340475492296275814398675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217787300656395034419198233 163340475492296275814398675)
    ·
      refine ⟨245010713238444413721598013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163340475492296275814398675 245010713238444413721598013)
      ·
        refine ⟨91879017464416655145599255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 245010713238444413721598013 91879017464416655145599255)
        ·
          refine ⟨137818526196624982718398883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91879017464416655145599255 137818526196624982718398883)
          ·
            refine ⟨206727789294937474077598325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137818526196624982718398883 206727789294937474077598325)
            ·
              refine ⟨19380730246400388194774843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 206727789294937474077598325 19380730246400388194774843)
              ·
                refine ⟨29071095369600582292162265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19380730246400388194774843 29071095369600582292162265)
                ·
                  refine ⟨21803321527200436719121699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29071095369600582292162265 21803321527200436719121699)
                  ·
                    refine ⟨32704982290800655078682549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21803321527200436719121699 32704982290800655078682549)
                    ·
                      refine ⟨3066092089762561413626489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32704982290800655078682549 3066092089762561413626489)
                      ·
                        rfl

theorem cell23_5971193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_5971193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5971193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5971193 prefixEnd_5971193 := by exact prefixLift 5971193
  have htrace : WordTrace (prefixWord ++ tailWord_5971193) baseStart_5971193 baseEnd_5971193 := by
    simpa [prefixWord, tailWord_5971193, baseEnd_5971193] using wordTrace_append hprefix tailTrace_5971193
  have hstable : (prefixWord ++ tailWord_5971193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5971193).length < 2 ^ (prefixWord ++ tailWord_5971193).sum := by decide
  have hdescent : baseEnd_5971193 < baseStart_5971193 := by decide
  rcases family_descends (prefixWord ++ tailWord_5971193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5971224 : List Nat := [2, 1, 2, 3, 1, 4, 1, 3, 2, 2, 2]
def baseStart_5971224 : Nat := 118140960795 + 5971224 * 2 ^ 59
def prefixEnd_5971224 : Nat := 4983230072969 + 3 ^ 40 * 5971224 * 2
def baseEnd_5971224 : Nat := 3066108007662850792338847

theorem tailTrace_5971224 : CollatzResearch.WordTrace tailWord_5971224 prefixEnd_5971224 3066108007662850792338847 := by
  unfold tailWord_5971224
  simp only [CollatzResearch.WordTrace]
  refine ⟨108894215659641363356788363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145192287546188484475717817 108894215659641363356788363)
  ·
    refine ⟨163341323489462045035182545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108894215659641363356788363 163341323489462045035182545)
    ·
      refine ⟨122505992617096533776386909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163341323489462045035182545 122505992617096533776386909)
      ·
        refine ⟨45939747231411200166145091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122505992617096533776386909 45939747231411200166145091)
        ·
          refine ⟨68909620847116800249217637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45939747231411200166145091 68909620847116800249217637)
          ·
            refine ⟨12920553908834400046728307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68909620847116800249217637 12920553908834400046728307)
            ·
              refine ⟨19380830863251600070092461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12920553908834400046728307 19380830863251600070092461)
              ·
                refine ⟨7267811573719350026284673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19380830863251600070092461 7267811573719350026284673)
                ·
                  refine ⟨5450858680289512519713505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7267811573719350026284673 5450858680289512519713505)
                  ·
                    refine ⟨4088144010217134389785129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5450858680289512519713505 4088144010217134389785129)
                    ·
                      refine ⟨3066108007662850792338847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4088144010217134389785129 3066108007662850792338847)
                      ·
                        rfl

theorem cell23_5971224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 3, 2, 2, 2].length) (baseStart_5971224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5971224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5971224 prefixEnd_5971224 := by exact prefixLift 5971224
  have htrace : WordTrace (prefixWord ++ tailWord_5971224) baseStart_5971224 baseEnd_5971224 := by
    simpa [prefixWord, tailWord_5971224, baseEnd_5971224] using wordTrace_append hprefix tailTrace_5971224
  have hstable : (prefixWord ++ tailWord_5971224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5971224).length < 2 ^ (prefixWord ++ tailWord_5971224).sum := by decide
  have hdescent : baseEnd_5971224 < baseStart_5971224 := by decide
  rcases family_descends (prefixWord ++ tailWord_5971224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5971260 : List Nat := [2, 2, 2, 2, 1, 3, 2, 2, 2, 5]
def baseStart_5971260 : Nat := 118140960795 + 5971260 * 2 ^ 59
def prefixEnd_5971260 : Nat := 4983230072969 + 3 ^ 40 * 5971260 * 2
def baseEnd_5971260 : Nat := 1022042164322137550496227

theorem tailTrace_5971260 : CollatzResearch.WordTrace tailWord_5971260 prefixEnd_5971260 1022042164322137550496227 := by
  unfold tailWord_5971260
  simp only [CollatzResearch.WordTrace]
  refine ⟨108894872173576152430943617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145193162898101536574591489 108894872173576152430943617)
  ·
    refine ⟨81671154130182114323207713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108894872173576152430943617 81671154130182114323207713)
    ·
      refine ⟨61253365597636585742405785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81671154130182114323207713 61253365597636585742405785)
      ·
        refine ⟨45940024198227439306804339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61253365597636585742405785 45940024198227439306804339)
        ·
          refine ⟨68910036297341158960206509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45940024198227439306804339 68910036297341158960206509)
          ·
            refine ⟨25841263611502934610077441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68910036297341158960206509 25841263611502934610077441)
            ·
              refine ⟨19380947708627200957558081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25841263611502934610077441 19380947708627200957558081)
              ·
                refine ⟨14535710781470400718168561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19380947708627200957558081 14535710781470400718168561)
                ·
                  refine ⟨10901783086102800538626421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14535710781470400718168561 10901783086102800538626421)
                  ·
                    refine ⟨1022042164322137550496227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10901783086102800538626421 1022042164322137550496227)
                    ·
                      rfl

theorem cell23_5971260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2, 2, 5].length) (baseStart_5971260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5971260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5971260 prefixEnd_5971260 := by exact prefixLift 5971260
  have htrace : WordTrace (prefixWord ++ tailWord_5971260) baseStart_5971260 baseEnd_5971260 := by
    simpa [prefixWord, tailWord_5971260, baseEnd_5971260] using wordTrace_append hprefix tailTrace_5971260
  have hstable : (prefixWord ++ tailWord_5971260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5971260).length < 2 ^ (prefixWord ++ tailWord_5971260).sum := by decide
  have hdescent : baseEnd_5971260 < baseStart_5971260 := by decide
  rcases family_descends (prefixWord ++ tailWord_5971260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5971290 : List Nat := [3, 1, 1, 2, 1, 2, 3, 1, 5, 4]
def baseStart_5971290 : Nat := 118140960795 + 5971290 * 2 ^ 59
def prefixEnd_5971290 : Nat := 4983230072969 + 3 ^ 40 * 5971290 * 2
def baseEnd_5971290 : Nat := 1022047299128682511371181

theorem tailTrace_5971290 : CollatzResearch.WordTrace tailWord_5971290 prefixEnd_5971290 1022047299128682511371181 := by
  unfold tailWord_5971290
  simp only [CollatzResearch.WordTrace]
  refine ⟨54447709634260904996369831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145193892358029079990319549 54447709634260904996369831)
  ·
    refine ⟨81671564451391357494554747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54447709634260904996369831 81671564451391357494554747)
    ·
      refine ⟨122507346677087036241832121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81671564451391357494554747 122507346677087036241832121)
      ·
        refine ⟨91880510007815277181374091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122507346677087036241832121 91880510007815277181374091)
        ·
          refine ⟨137820765011722915772061137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91880510007815277181374091 137820765011722915772061137)
          ·
            refine ⟨103365573758792186829045853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137820765011722915772061137 103365573758792186829045853)
            ·
              refine ⟨38762090159547070060892195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103365573758792186829045853 38762090159547070060892195)
              ·
                refine ⟨58143135239320605091338293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38762090159547070060892195 58143135239320605091338293)
                ·
                  refine ⟨5450918928686306727312965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58143135239320605091338293 5450918928686306727312965)
                  ·
                    refine ⟨1022047299128682511371181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5450918928686306727312965 1022047299128682511371181)
                    ·
                      rfl

theorem cell23_5971290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 5, 4].length) (baseStart_5971290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5971290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5971290 prefixEnd_5971290 := by exact prefixLift 5971290
  have htrace : WordTrace (prefixWord ++ tailWord_5971290) baseStart_5971290 baseEnd_5971290 := by
    simpa [prefixWord, tailWord_5971290, baseEnd_5971290] using wordTrace_append hprefix tailTrace_5971290
  have hstable : (prefixWord ++ tailWord_5971290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5971290).length < 2 ^ (prefixWord ++ tailWord_5971290).sum := by decide
  have hdescent : baseEnd_5971290 < baseStart_5971290 := by decide
  rcases family_descends (prefixWord ++ tailWord_5971290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5971323 : List Nat := [1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 8]
def baseStart_5971323 : Nat := 118140960795 + 5971323 * 2 ^ 59
def prefixEnd_5971323 : Nat := 4983230072969 + 3 ^ 40 * 5971323 * 2
def baseEnd_5971323 : Nat := 3066158842247645905000891

theorem tailTrace_5971323 : CollatzResearch.WordTrace tailWord_5971323 prefixEnd_5971323 3066158842247645905000891 := by
  unfold tailWord_5971323
  simp only [CollatzResearch.WordTrace]
  refine ⟨217792042145924066621430623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145194694763949377747620415 217792042145924066621430623)
  ·
    refine ⟨326688063218886099932145935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217792042145924066621430623 326688063218886099932145935)
    ·
      refine ⟨490032094828329149898218903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326688063218886099932145935 490032094828329149898218903)
      ·
        refine ⟨735048142242493724847328355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 490032094828329149898218903 735048142242493724847328355)
        ·
          refine ⟨1102572213363740587270992533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 735048142242493724847328355 1102572213363740587270992533)
          ·
            refine ⟨51683072501425340028327775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1102572213363740587270992533 51683072501425340028327775)
            ·
              refine ⟨77524608752138010042491663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51683072501425340028327775 77524608752138010042491663)
              ·
                refine ⟨116286913128207015063737495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77524608752138010042491663 116286913128207015063737495)
                ·
                  refine ⟨174430369692310522595606243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116286913128207015063737495 174430369692310522595606243)
                  ·
                    refine ⟨261645554538465783893409365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 174430369692310522595606243 261645554538465783893409365)
                    ·
                      refine ⟨3066158842247645905000891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 261645554538465783893409365 3066158842247645905000891)
                      ·
                        rfl

theorem cell23_5971323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 8].length) (baseStart_5971323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5971323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5971323 prefixEnd_5971323 := by exact prefixLift 5971323
  have htrace : WordTrace (prefixWord ++ tailWord_5971323) baseStart_5971323 baseEnd_5971323 := by
    simpa [prefixWord, tailWord_5971323, baseEnd_5971323] using wordTrace_append hprefix tailTrace_5971323
  have hstable : (prefixWord ++ tailWord_5971323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5971323).length < 2 ^ (prefixWord ++ tailWord_5971323).sum := by decide
  have hdescent : baseEnd_5971323 < baseStart_5971323 := by decide
  rcases family_descends (prefixWord ++ tailWord_5971323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5971367 : List Nat := [1, 1, 6, 1, 1, 1, 1, 5, 1, 5]
def baseStart_5971367 : Nat := 118140960795 + 5971367 * 2 ^ 59
def prefixEnd_5971367 : Nat := 4983230072969 + 3 ^ 40 * 5971367 * 2
def baseEnd_5971367 : Nat := 1022060478465481244283563

theorem tailTrace_5971367 : CollatzResearch.WordTrace tailWord_5971367 prefixEnd_5971367 1022060478465481244283563 := by
  unfold tailWord_5971367
  simp only [CollatzResearch.WordTrace]
  refine ⟨217793646957764662136032355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145195764638509774757354903 217793646957764662136032355)
  ·
    refine ⟨326690470436646993204048533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217793646957764662136032355 326690470436646993204048533)
    ·
      refine ⟨15313615801717827806439775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 326690470436646993204048533 15313615801717827806439775)
      ·
        refine ⟨22970423702576741709659663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15313615801717827806439775 22970423702576741709659663)
        ·
          refine ⟨34455635553865112564489495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22970423702576741709659663 34455635553865112564489495)
          ·
            refine ⟨51683453330797668846734243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34455635553865112564489495 51683453330797668846734243)
            ·
              refine ⟨77525179996196503270101365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51683453330797668846734243 77525179996196503270101365)
              ·
                refine ⟨7267985624643422181572003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77525179996196503270101365 7267985624643422181572003)
                ·
                  refine ⟨10901978436965133272358005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7267985624643422181572003 10901978436965133272358005)
                  ·
                    refine ⟨1022060478465481244283563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10901978436965133272358005 1022060478465481244283563)
                    ·
                      rfl

theorem cell23_5971367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_5971367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5971367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5971367 prefixEnd_5971367 := by exact prefixLift 5971367
  have htrace : WordTrace (prefixWord ++ tailWord_5971367) baseStart_5971367 baseEnd_5971367 := by
    simpa [prefixWord, tailWord_5971367, baseEnd_5971367] using wordTrace_append hprefix tailTrace_5971367
  have hstable : (prefixWord ++ tailWord_5971367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5971367).length < 2 ^ (prefixWord ++ tailWord_5971367).sum := by decide
  have hdescent : baseEnd_5971367 < baseStart_5971367 := by decide
  rcases family_descends (prefixWord ++ tailWord_5971367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5971381 : List Nat := [1, 3, 3, 2, 2, 3, 1, 1, 3, 1, 3]
def baseStart_5971381 : Nat := 118140960795 + 5971381 * 2 ^ 59
def prefixEnd_5971381 : Nat := 4983230072969 + 3 ^ 40 * 5971381 * 2
def baseEnd_5971381 : Nat := 3066188624125606678075625

theorem tailTrace_5971381 : CollatzResearch.WordTrace tailWord_5971381 prefixEnd_5971381 3066188624125606678075625 := by
  unfold tailWord_5971381
  simp only [CollatzResearch.WordTrace]
  refine ⟨217794157579713942527041997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145196105053142628351361331 217794157579713942527041997)
  ·
    refine ⟨81672809092392728447640749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217794157579713942527041997 81672809092392728447640749)
    ·
      refine ⟨30627303409647273167865281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81672809092392728447640749 30627303409647273167865281)
      ·
        refine ⟨22970477557235454875898961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30627303409647273167865281 22970477557235454875898961)
        ·
          refine ⟨17227858167926591156924221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22970477557235454875898961 17227858167926591156924221)
          ·
            refine ⟨6460446812972471683846583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17227858167926591156924221 6460446812972471683846583)
            ·
              refine ⟨9690670219458707525769875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6460446812972471683846583 9690670219458707525769875)
              ·
                refine ⟨14536005329188061288654813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9690670219458707525769875 14536005329188061288654813)
                ·
                  refine ⟨5451001998445522983245555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14536005329188061288654813 5451001998445522983245555)
                  ·
                    refine ⟨8176502997668284474868333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5451001998445522983245555 8176502997668284474868333)
                    ·
                      refine ⟨3066188624125606678075625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8176502997668284474868333 3066188624125606678075625)
                      ·
                        rfl

theorem cell23_5971381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_5971381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5971381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5971381 prefixEnd_5971381 := by exact prefixLift 5971381
  have htrace : WordTrace (prefixWord ++ tailWord_5971381) baseStart_5971381 baseEnd_5971381 := by
    simpa [prefixWord, tailWord_5971381, baseEnd_5971381] using wordTrace_append hprefix tailTrace_5971381
  have hstable : (prefixWord ++ tailWord_5971381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5971381).length < 2 ^ (prefixWord ++ tailWord_5971381).sum := by decide
  have hdescent : baseEnd_5971381 < baseStart_5971381 := by decide
  rcases family_descends (prefixWord ++ tailWord_5971381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5971400 : List Nat := [2, 1, 3, 1, 3, 1, 1, 3, 1, 1, 6]
def baseStart_5971400 : Nat := 118140960795 + 5971400 * 2 ^ 59
def prefixEnd_5971400 : Nat := 4983230072969 + 3 ^ 40 * 5971400 * 2
def baseEnd_5971400 : Nat := 3066198380258042103738037

theorem tailTrace_5971400 : CollatzResearch.WordTrace tailWord_5971400 prefixEnd_5971400 3066198380258042103738037 := by
  unfold tailWord_5971400
  simp only [CollatzResearch.WordTrace]
  refine ⟨108897425283322554385991827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145196567044430072514655769 108897425283322554385991827)
  ·
    refine ⟨163346137924983831578987741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108897425283322554385991827 163346137924983831578987741)
    ·
      refine ⟨61254801721868936842120403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163346137924983831578987741 61254801721868936842120403)
      ·
        refine ⟨91882202582803405263180605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61254801721868936842120403 91882202582803405263180605)
        ·
          refine ⟨34455825968551276973692727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91882202582803405263180605 34455825968551276973692727)
          ·
            refine ⟨51683738952826915460539091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34455825968551276973692727 51683738952826915460539091)
            ·
              refine ⟨77525608429240373190808637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51683738952826915460539091 77525608429240373190808637)
              ·
                refine ⟨29072103160965139946553239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77525608429240373190808637 29072103160965139946553239)
                ·
                  refine ⟨43608154741447709919829859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29072103160965139946553239 43608154741447709919829859)
                  ·
                    refine ⟨65412232112171564879744789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43608154741447709919829859 65412232112171564879744789)
                    ·
                      refine ⟨3066198380258042103738037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65412232112171564879744789 3066198380258042103738037)
                      ·
                        rfl

theorem cell23_5971400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_5971400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5971400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5971400 prefixEnd_5971400 := by exact prefixLift 5971400
  have htrace : WordTrace (prefixWord ++ tailWord_5971400) baseStart_5971400 baseEnd_5971400 := by
    simpa [prefixWord, tailWord_5971400, baseEnd_5971400] using wordTrace_append hprefix tailTrace_5971400
  have hstable : (prefixWord ++ tailWord_5971400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5971400).length < 2 ^ (prefixWord ++ tailWord_5971400).sum := by decide
  have hdescent : baseEnd_5971400 < baseStart_5971400 := by decide
  rcases family_descends (prefixWord ++ tailWord_5971400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5971404 : List Nat := [2, 2, 1, 4, 2, 1, 3, 2, 1, 1, 4]
def baseStart_5971404 : Nat := 118140960795 + 5971404 * 2 ^ 59
def prefixEnd_5971404 : Nat := 4983230072969 + 3 ^ 40 * 5971404 * 2
def baseEnd_5971404 : Nat := 3066200434180660088088019

theorem tailTrace_5971404 : CollatzResearch.WordTrace tailWord_5971404 prefixEnd_5971404 3066200434180660088088019 := by
  unfold tailWord_5971404
  simp only [CollatzResearch.WordTrace]
  refine ⟨108897498229315308727564633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145196664305753744970086177 108897498229315308727564633)
  ·
    refine ⟨81673123671986481545673475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108897498229315308727564633 81673123671986481545673475)
    ·
      refine ⟨122509685507979722318510213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81673123671986481545673475 122509685507979722318510213)
      ·
        refine ⟨22970566032746197934720665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122509685507979722318510213 22970566032746197934720665)
        ·
          refine ⟨17227924524559648451040499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22970566032746197934720665 17227924524559648451040499)
          ·
            refine ⟨25841886786839472676560749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17227924524559648451040499 25841886786839472676560749)
            ·
              refine ⟨9690707545064802253710281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25841886786839472676560749 9690707545064802253710281)
              ·
                refine ⟨7268030658798601690282711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9690707545064802253710281 7268030658798601690282711)
                ·
                  refine ⟨10902045988197902535424067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7268030658798601690282711 10902045988197902535424067)
                  ·
                    refine ⟨16353068982296853803136101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10902045988197902535424067 16353068982296853803136101)
                    ·
                      refine ⟨3066200434180660088088019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16353068982296853803136101 3066200434180660088088019)
                      ·
                        rfl

theorem cell23_5971404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_5971404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5971404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5971404 prefixEnd_5971404 := by exact prefixLift 5971404
  have htrace : WordTrace (prefixWord ++ tailWord_5971404) baseStart_5971404 baseEnd_5971404 := by
    simpa [prefixWord, tailWord_5971404, baseEnd_5971404] using wordTrace_append hprefix tailTrace_5971404
  have hstable : (prefixWord ++ tailWord_5971404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5971404).length < 2 ^ (prefixWord ++ tailWord_5971404).sum := by decide
  have hdescent : baseEnd_5971404 < baseStart_5971404 := by decide
  rcases family_descends (prefixWord ++ tailWord_5971404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5971414 : List Nat := [5, 2, 1, 1, 1, 3, 1, 2, 1, 6]
def baseStart_5971414 : Nat := 118140960795 + 5971414 * 2 ^ 59
def prefixEnd_5971414 : Nat := 4983230072969 + 3 ^ 40 * 5971414 * 2
def baseEnd_5971414 : Nat := 1022068522995735016320991

theorem tailTrace_5971414 : CollatzResearch.WordTrace tailWord_5971414 prefixEnd_5971414 1022068522995735016320991 := by
  unfold tailWord_5971414
  simp only [CollatzResearch.WordTrace]
  refine ⟨13612210074287149322687081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145196907459062926108662197 13612210074287149322687081)
  ·
    refine ⟨10209157555715361992015311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13612210074287149322687081 10209157555715361992015311)
    ·
      refine ⟨15313736333573042988022967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10209157555715361992015311 15313736333573042988022967)
      ·
        refine ⟨22970604500359564482034451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15313736333573042988022967 22970604500359564482034451)
        ·
          refine ⟨34455906750539346723051677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22970604500359564482034451 34455906750539346723051677)
          ·
            refine ⟨12920965031452255021144379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34455906750539346723051677 12920965031452255021144379)
            ·
              refine ⟨19381447547178382531716569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12920965031452255021144379 19381447547178382531716569)
              ·
                refine ⟨14536085660383786898787427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19381447547178382531716569 14536085660383786898787427)
                ·
                  refine ⟨21804128490575680348181141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14536085660383786898787427 21804128490575680348181141)
                  ·
                    refine ⟨1022068522995735016320991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21804128490575680348181141 1022068522995735016320991)
                    ·
                      rfl

theorem cell23_5971414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_5971414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5971414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5971414 prefixEnd_5971414 := by exact prefixLift 5971414
  have htrace : WordTrace (prefixWord ++ tailWord_5971414) baseStart_5971414 baseEnd_5971414 := by
    simpa [prefixWord, tailWord_5971414, baseEnd_5971414] using wordTrace_append hprefix tailTrace_5971414
  have hstable : (prefixWord ++ tailWord_5971414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5971414).length < 2 ^ (prefixWord ++ tailWord_5971414).sum := by decide
  have hdescent : baseEnd_5971414 < baseStart_5971414 := by decide
  rcases family_descends (prefixWord ++ tailWord_5971414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5971417 : List Nat := [1, 2, 1, 2, 4, 3, 1, 2, 1, 2, 4]
def baseStart_5971417 : Nat := 118140960795 + 5971417 * 2 ^ 59
def prefixEnd_5971417 : Nat := 4983230072969 + 3 ^ 40 * 5971417 * 2
def baseEnd_5971417 : Nat := 3066207109429168537225459

theorem tailTrace_5971417 : CollatzResearch.WordTrace tailWord_5971417 prefixEnd_5971417 3066207109429168537225459 := by
  unfold tailWord_5971417
  simp only [CollatzResearch.WordTrace]
  refine ⟨217795470607583520675352505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145196980405055680450235003 217795470607583520675352505)
  ·
    refine ⟨163346602955687640506514379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217795470607583520675352505 163346602955687640506514379)
    ·
      refine ⟨245019904433531460759771569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163346602955687640506514379 245019904433531460759771569)
      ·
        refine ⟨183764928325148595569828677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245019904433531460759771569 183764928325148595569828677)
        ·
          refine ⟨34455924060965361669342877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 183764928325148595569828677 34455924060965361669342877)
          ·
            refine ⟨12920971522862010626003579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34455924060965361669342877 12920971522862010626003579)
            ·
              refine ⟨19381457284293015939005369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12920971522862010626003579 19381457284293015939005369)
              ·
                refine ⟨14536092963219761954254027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19381457284293015939005369 14536092963219761954254027)
                ·
                  refine ⟨21804139444829642931381041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14536092963219761954254027 21804139444829642931381041)
                  ·
                    refine ⟨16353104583622232198535781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21804139444829642931381041 16353104583622232198535781)
                    ·
                      refine ⟨3066207109429168537225459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16353104583622232198535781 3066207109429168537225459)
                      ·
                        rfl

theorem cell23_5971417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 2, 1, 2, 4].length) (baseStart_5971417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5971417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5971417 prefixEnd_5971417 := by exact prefixLift 5971417
  have htrace : WordTrace (prefixWord ++ tailWord_5971417) baseStart_5971417 baseEnd_5971417 := by
    simpa [prefixWord, tailWord_5971417, baseEnd_5971417] using wordTrace_append hprefix tailTrace_5971417
  have hstable : (prefixWord ++ tailWord_5971417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5971417).length < 2 ^ (prefixWord ++ tailWord_5971417).sum := by decide
  have hdescent : baseEnd_5971417 < baseStart_5971417 := by decide
  rcases family_descends (prefixWord ++ tailWord_5971417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5971421 : List Nat := [1, 4, 3, 1, 1, 3, 3, 1, 1, 1, 4]
def baseStart_5971421 : Nat := 118140960795 + 5971421 * 2 ^ 59
def prefixEnd_5971421 : Nat := 4983230072969 + 3 ^ 40 * 5971421 * 2
def baseEnd_5971421 : Nat := 3066209163351786521575441

theorem tailTrace_5971421 : CollatzResearch.WordTrace tailWord_5971421 prefixEnd_5971421 3066209163351786521575441 := by
  unfold tailWord_5971421
  simp only [CollatzResearch.WordTrace]
  refine ⟨217795616499569029358498117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145197077666379352905665411 217795616499569029358498117)
  ·
    refine ⟨40836678093669193004718397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 217795616499569029358498117 40836678093669193004718397)
    ·
      refine ⟨15313754285125947376769399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40836678093669193004718397 15313754285125947376769399)
      ·
        refine ⟨22970631427688921065154099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15313754285125947376769399 22970631427688921065154099)
        ·
          refine ⟨34455947141533381597731149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22970631427688921065154099 34455947141533381597731149)
          ·
            refine ⟨12920980178075018099149181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34455947141533381597731149 12920980178075018099149181)
            ·
              refine ⟨4845367566778131787180943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12920980178075018099149181 4845367566778131787180943)
              ·
                refine ⟨7268051350167197680771415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4845367566778131787180943 7268051350167197680771415)
                ·
                  refine ⟨10902077025250796521157123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7268051350167197680771415 10902077025250796521157123)
                  ·
                    refine ⟨16353115537876194781735685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10902077025250796521157123 16353115537876194781735685)
                    ·
                      refine ⟨3066209163351786521575441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16353115537876194781735685 3066209163351786521575441)
                      ·
                        rfl

theorem cell23_5971421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_5971421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5971421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5971421 prefixEnd_5971421 := by exact prefixLift 5971421
  have htrace : WordTrace (prefixWord ++ tailWord_5971421) baseStart_5971421 baseEnd_5971421 := by
    simpa [prefixWord, tailWord_5971421, baseEnd_5971421] using wordTrace_append hprefix tailTrace_5971421
  have hstable : (prefixWord ++ tailWord_5971421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5971421).length < 2 ^ (prefixWord ++ tailWord_5971421).sum := by decide
  have hdescent : baseEnd_5971421 < baseStart_5971421 := by decide
  rcases family_descends (prefixWord ++ tailWord_5971421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5971438 : List Nat := [4, 1, 2, 1, 2, 1, 3, 4, 1, 2, 2]
def baseStart_5971438 : Nat := 118140960795 + 5971438 * 2 ^ 59
def prefixEnd_5971438 : Nat := 4983230072969 + 3 ^ 40 * 5971438 * 2
def baseEnd_5971438 : Nat := 3066217892522912955062863

theorem tailTrace_5971438 : CollatzResearch.WordTrace tailWord_5971438 prefixEnd_5971438 3066217892522912955062863 := by
  unfold tailWord_5971438
  simp only [CollatzResearch.WordTrace]
  refine ⟨27224529567563430157733371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145197491027004960841244645 27224529567563430157733371)
  ·
    refine ⟨40836794351345145236600057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27224529567563430157733371 40836794351345145236600057)
    ·
      refine ⟨30627595763508858927450043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40836794351345145236600057 30627595763508858927450043)
      ·
        refine ⟨45941393645263288391175065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30627595763508858927450043 45941393645263288391175065)
        ·
          refine ⟨34456045233947466293381299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45941393645263288391175065 34456045233947466293381299)
          ·
            refine ⟨51684067850921199440071949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34456045233947466293381299 51684067850921199440071949)
            ·
              refine ⟨19381525444095449790026981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51684067850921199440071949 19381525444095449790026981)
              ·
                refine ⟨3634036020767896835630059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19381525444095449790026981 3634036020767896835630059)
                ·
                  refine ⟨5451054031151845253445089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3634036020767896835630059 5451054031151845253445089)
                  ·
                    refine ⟨4088290523363883940083817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5451054031151845253445089 4088290523363883940083817)
                    ·
                      refine ⟨3066217892522912955062863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4088290523363883940083817 3066217892522912955062863)
                      ·
                        rfl

theorem cell23_5971438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 4, 1, 2, 2].length) (baseStart_5971438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5971438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5971438 prefixEnd_5971438 := by exact prefixLift 5971438
  have htrace : WordTrace (prefixWord ++ tailWord_5971438) baseStart_5971438 baseEnd_5971438 := by
    simpa [prefixWord, tailWord_5971438, baseEnd_5971438] using wordTrace_append hprefix tailTrace_5971438
  have hstable : (prefixWord ++ tailWord_5971438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5971438).length < 2 ^ (prefixWord ++ tailWord_5971438).sum := by decide
  have hdescent : baseEnd_5971438 < baseStart_5971438 := by decide
  rcases family_descends (prefixWord ++ tailWord_5971438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5971440 : List Nat := [2, 1, 1, 1, 3, 4, 1, 1, 2, 7]
def baseStart_5971440 : Nat := 118140960795 + 5971440 * 2 ^ 59
def prefixEnd_5971440 : Nat := 4983230072969 + 3 ^ 40 * 5971440 * 2
def baseEnd_5971440 : Nat := 1022072973161407315745951

theorem tailTrace_5971440 : CollatzResearch.WordTrace tailWord_5971440 prefixEnd_5971440 1022072973161407315745951 := by
  unfold tailWord_5971440
  simp only [CollatzResearch.WordTrace]
  refine ⟨108898154743250097801719887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145197539657666797068959849 108898154743250097801719887)
  ·
    refine ⟨163347232114875146702579831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108898154743250097801719887 163347232114875146702579831)
    ·
      refine ⟨245020848172312720053869747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163347232114875146702579831 245020848172312720053869747)
      ·
        refine ⟨367531272258469080080804621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245020848172312720053869747 367531272258469080080804621)
        ·
          refine ⟨137824227096925905030301733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 367531272258469080080804621 137824227096925905030301733)
          ·
            refine ⟨25842042580673607193181575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 137824227096925905030301733 25842042580673607193181575)
            ·
              refine ⟨38763063871010410789772363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25842042580673607193181575 38763063871010410789772363)
              ·
                refine ⟨58144595806515616184658545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38763063871010410789772363 58144595806515616184658545)
                ·
                  refine ⟨43608446854886712138493909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58144595806515616184658545 43608446854886712138493909)
                  ·
                    refine ⟨1022072973161407315745951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43608446854886712138493909 1022072973161407315745951)
                    ·
                      rfl

theorem cell23_5971440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 2, 7].length) (baseStart_5971440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5971440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5971440 prefixEnd_5971440 := by exact prefixLift 5971440
  have htrace : WordTrace (prefixWord ++ tailWord_5971440) baseStart_5971440 baseEnd_5971440 := by
    simpa [prefixWord, tailWord_5971440, baseEnd_5971440] using wordTrace_append hprefix tailTrace_5971440
  have hstable : (prefixWord ++ tailWord_5971440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5971440).length < 2 ^ (prefixWord ++ tailWord_5971440).sum := by decide
  have hdescent : baseEnd_5971440 < baseStart_5971440 := by decide
  rcases family_descends (prefixWord ++ tailWord_5971440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5971464 : List Nat := [2, 1, 3, 2, 1, 1, 4, 1, 3, 3, 2]
def baseStart_5971464 : Nat := 118140960795 + 5971464 * 2 ^ 59
def prefixEnd_5971464 : Nat := 4983230072969 + 3 ^ 40 * 5971464 * 2
def baseEnd_5971464 : Nat := 3066231243019929853337743

theorem tailTrace_5971464 : CollatzResearch.WordTrace tailWord_5971464 prefixEnd_5971464 3066231243019929853337743 := by
  unfold tailWord_5971464
  simp only [CollatzResearch.WordTrace]
  refine ⟨108898592419206623851156723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145198123225608831801542297 108898592419206623851156723)
  ·
    refine ⟨163347888628809935776735085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108898592419206623851156723 163347888628809935776735085)
    ·
      refine ⟨61255458235803725916275657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163347888628809935776735085 61255458235803725916275657)
      ·
        refine ⟨45941593676852794437206743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61255458235803725916275657 45941593676852794437206743)
        ·
          refine ⟨68912390515279191655810115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45941593676852794437206743 68912390515279191655810115)
          ·
            refine ⟨103368585772918787483715173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68912390515279191655810115 103368585772918787483715173)
            ·
              refine ⟨19381609832422272653196595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103368585772918787483715173 19381609832422272653196595)
              ·
                refine ⟨29072414748633408979794893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19381609832422272653196595 29072414748633408979794893)
                ·
                  refine ⟨10902155530737528367423085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29072414748633408979794893 10902155530737528367423085)
                  ·
                    refine ⟨4088308324026573137783657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10902155530737528367423085 4088308324026573137783657)
                    ·
                      refine ⟨3066231243019929853337743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4088308324026573137783657 3066231243019929853337743)
                      ·
                        rfl

theorem cell23_5971464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 3, 3, 2].length) (baseStart_5971464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5971464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5971464 prefixEnd_5971464 := by exact prefixLift 5971464
  have htrace : WordTrace (prefixWord ++ tailWord_5971464) baseStart_5971464 baseEnd_5971464 := by
    simpa [prefixWord, tailWord_5971464, baseEnd_5971464] using wordTrace_append hprefix tailTrace_5971464
  have hstable : (prefixWord ++ tailWord_5971464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5971464).length < 2 ^ (prefixWord ++ tailWord_5971464).sum := by decide
  have hdescent : baseEnd_5971464 < baseStart_5971464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5971464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5971488 : List Nat := [2, 1, 1, 6, 1, 3, 1, 2, 2, 1, 3]
def baseStart_5971488 : Nat := 118140960795 + 5971488 * 2 ^ 59
def prefixEnd_5971488 : Nat := 4983230072969 + 3 ^ 40 * 5971488 * 2
def baseEnd_5971488 : Nat := 3066243566555637759437633

theorem tailTrace_5971488 : CollatzResearch.WordTrace tailWord_5971488 prefixEnd_5971488 3066243566555637759437633 := by
  unfold tailWord_5971488
  simp only [CollatzResearch.WordTrace]
  refine ⟨108899030095163149900593559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145198706793550866534124745 108899030095163149900593559)
  ·
    refine ⟨163348545142744724850890339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108899030095163149900593559 163348545142744724850890339)
    ·
      refine ⟨245022817714117087276335509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163348545142744724850890339 245022817714117087276335509)
      ·
        refine ⟨11485444580349238466078227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 245022817714117087276335509 11485444580349238466078227)
        ·
          refine ⟨17228166870523857699117341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11485444580349238466078227 17228166870523857699117341)
          ·
            refine ⟨6460562576446446637169003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17228166870523857699117341 6460562576446446637169003)
            ·
              refine ⟨9690843864669669955753505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6460562576446446637169003 9690843864669669955753505)
              ·
                refine ⟨7268132898502252466815129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9690843864669669955753505 7268132898502252466815129)
                ·
                  refine ⟨5451099673876689350111347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7268132898502252466815129 5451099673876689350111347)
                  ·
                    refine ⟨8176649510815034025167021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5451099673876689350111347 8176649510815034025167021)
                    ·
                      refine ⟨3066243566555637759437633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8176649510815034025167021 3066243566555637759437633)
                      ·
                        rfl

theorem cell23_5971488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_5971488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5971488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5971488 prefixEnd_5971488 := by exact prefixLift 5971488
  have htrace : WordTrace (prefixWord ++ tailWord_5971488) baseStart_5971488 baseEnd_5971488 := by
    simpa [prefixWord, tailWord_5971488, baseEnd_5971488] using wordTrace_append hprefix tailTrace_5971488
  have hstable : (prefixWord ++ tailWord_5971488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5971488).length < 2 ^ (prefixWord ++ tailWord_5971488).sum := by decide
  have hdescent : baseEnd_5971488 < baseStart_5971488 := by decide
  rcases family_descends (prefixWord ++ tailWord_5971488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5971507 : List Nat := [1, 1, 1, 2, 4, 3, 2, 1, 2, 2, 4]
def baseStart_5971507 : Nat := 118140960795 + 5971507 * 2 ^ 59
def prefixEnd_5971507 : Nat := 4983230072969 + 3 ^ 40 * 5971507 * 2
def baseEnd_5971507 : Nat := 3066253322688073185100045

theorem tailTrace_5971507 : CollatzResearch.WordTrace tailWord_5971507 prefixEnd_5971507 3066253322688073185100045 := by
  unfold tailWord_5971507
  simp only [CollatzResearch.WordTrace]
  refine ⟨217798753177257466046128775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145199168784838310697419183 217798753177257466046128775)
  ·
    refine ⟨326698129765886199069193163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217798753177257466046128775 326698129765886199069193163)
    ·
      refine ⟨490047194648829298603789745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326698129765886199069193163 490047194648829298603789745)
      ·
        refine ⟨367535395986621973952842309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 490047194648829298603789745 367535395986621973952842309)
        ·
          refine ⟨68912886747491620116157933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 367535395986621973952842309 68912886747491620116157933)
          ·
            refine ⟨25842332530309357543559225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68912886747491620116157933 25842332530309357543559225)
            ·
              refine ⟨19381749397732018157669419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25842332530309357543559225 19381749397732018157669419)
              ·
                refine ⟨29072624096598027236504129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19381749397732018157669419 29072624096598027236504129)
                ·
                  refine ⟨21804468072448520427378097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29072624096598027236504129 21804468072448520427378097)
                  ·
                    refine ⟨16353351054336390320533573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21804468072448520427378097 16353351054336390320533573)
                    ·
                      refine ⟨3066253322688073185100045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16353351054336390320533573 3066253322688073185100045)
                      ·
                        rfl

theorem cell23_5971507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 2, 2, 4].length) (baseStart_5971507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5971507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5971507 prefixEnd_5971507 := by exact prefixLift 5971507
  have htrace : WordTrace (prefixWord ++ tailWord_5971507) baseStart_5971507 baseEnd_5971507 := by
    simpa [prefixWord, tailWord_5971507, baseEnd_5971507] using wordTrace_append hprefix tailTrace_5971507
  have hstable : (prefixWord ++ tailWord_5971507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5971507).length < 2 ^ (prefixWord ++ tailWord_5971507).sum := by decide
  have hdescent : baseEnd_5971507 < baseStart_5971507 := by decide
  rcases family_descends (prefixWord ++ tailWord_5971507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5971511 : List Nat := [1, 1, 3, 1, 2, 6, 1, 1, 1, 4, 2]
def baseStart_5971511 : Nat := 118140960795 + 5971511 * 2 ^ 59
def prefixEnd_5971511 : Nat := 4983230072969 + 3 ^ 40 * 5971511 * 2
def baseEnd_5971511 : Nat := 3066255376610691169450027

theorem tailTrace_5971511 : CollatzResearch.WordTrace tailWord_5971511 prefixEnd_5971511 3066255376610691169450027 := by
  unfold tailWord_5971511
  simp only [CollatzResearch.WordTrace]
  refine ⟨217798899069242974729274387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145199266046161983152849591 217798899069242974729274387)
  ·
    refine ⟨326698348603864462093911581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217798899069242974729274387 326698348603864462093911581)
    ·
      refine ⟨122511880726449173285216843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 326698348603864462093911581 122511880726449173285216843)
      ·
        refine ⟨183767821089673759927825265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122511880726449173285216843 183767821089673759927825265)
        ·
          refine ⟨137825865817255319945868949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183767821089673759927825265 137825865817255319945868949)
          ·
            refine ⟨6460587460183843122462607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 137825865817255319945868949 6460587460183843122462607)
            ·
              refine ⟨9690881190275764683693911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6460587460183843122462607 9690881190275764683693911)
              ·
                refine ⟨14536321785413647025540867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9690881190275764683693911 14536321785413647025540867)
                ·
                  refine ⟨21804482678120470538311301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14536321785413647025540867 21804482678120470538311301)
                  ·
                    refine ⟨4088340502147588225933369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21804482678120470538311301 4088340502147588225933369)
                    ·
                      refine ⟨3066255376610691169450027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4088340502147588225933369 3066255376610691169450027)
                      ·
                        rfl

theorem cell23_5971511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 1, 1, 4, 2].length) (baseStart_5971511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5971511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5971511 prefixEnd_5971511 := by exact prefixLift 5971511
  have htrace : WordTrace (prefixWord ++ tailWord_5971511) baseStart_5971511 baseEnd_5971511 := by
    simpa [prefixWord, tailWord_5971511, baseEnd_5971511] using wordTrace_append hprefix tailTrace_5971511
  have hstable : (prefixWord ++ tailWord_5971511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5971511).length < 2 ^ (prefixWord ++ tailWord_5971511).sum := by decide
  have hdescent : baseEnd_5971511 < baseStart_5971511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5971511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5971557 : List Nat := [1, 3, 1, 3, 3, 1, 1, 1, 1, 1, 7]
def baseStart_5971557 : Nat := 118140960795 + 5971557 * 2 ^ 59
def prefixEnd_5971557 : Nat := 4983230072969 + 3 ^ 40 * 5971557 * 2
def baseEnd_5971557 : Nat := 3066278996720797989474815

theorem tailTrace_5971557 : CollatzResearch.WordTrace tailWord_5971557 prefixEnd_5971557 3066278996720797989474815 := by
  unfold tailWord_5971557
  simp only [CollatzResearch.WordTrace]
  refine ⟨217800576827076324585448925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145200384551384216390299283 217800576827076324585448925)
  ·
    refine ⟨81675216310153621719543347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217800576827076324585448925 81675216310153621719543347)
    ·
      refine ⟨122512824465230432579315021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81675216310153621719543347 122512824465230432579315021)
      ·
        refine ⟨45942309174461412217243133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122512824465230432579315021 45942309174461412217243133)
        ·
          refine ⟨17228365940423029581466175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45942309174461412217243133 17228365940423029581466175)
          ·
            refine ⟨25842548910634544372199263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17228365940423029581466175 25842548910634544372199263)
            ·
              refine ⟨38763823365951816558298895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25842548910634544372199263 38763823365951816558298895)
              ·
                refine ⟨58145735048927724837448343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38763823365951816558298895 58145735048927724837448343)
                ·
                  refine ⟨87218602573391587256172515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58145735048927724837448343 87218602573391587256172515)
                  ·
                    refine ⟨130827903860087380884258773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 87218602573391587256172515 130827903860087380884258773)
                    ·
                      refine ⟨3066278996720797989474815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 130827903860087380884258773 3066278996720797989474815)
                      ·
                        rfl

theorem cell23_5971557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_5971557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5971557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5971557 prefixEnd_5971557 := by exact prefixLift 5971557
  have htrace : WordTrace (prefixWord ++ tailWord_5971557) baseStart_5971557 baseEnd_5971557 := by
    simpa [prefixWord, tailWord_5971557, baseEnd_5971557] using wordTrace_append hprefix tailTrace_5971557
  have hstable : (prefixWord ++ tailWord_5971557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5971557).length < 2 ^ (prefixWord ++ tailWord_5971557).sum := by decide
  have hdescent : baseEnd_5971557 < baseStart_5971557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5971557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5971567 : List Nat := [1, 1, 2, 1, 3, 2, 1, 1, 6, 1, 4]
def baseStart_5971567 : Nat := 118140960795 + 5971567 * 2 ^ 59
def prefixEnd_5971567 : Nat := 4983230072969 + 3 ^ 40 * 5971567 * 2
def baseEnd_5971567 : Nat := 3066284131527342950349769

theorem tailTrace_5971567 : CollatzResearch.WordTrace tailWord_5971567 prefixEnd_5971567 3066284131527342950349769 := by
  unfold tailWord_5971567
  simp only [CollatzResearch.WordTrace]
  refine ⟨217800941557040096293312955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145200627704693397528875303 217800941557040096293312955)
  ·
    refine ⟨326701412335560144439969433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217800941557040096293312955 326701412335560144439969433)
    ·
      refine ⟨245026059251670108329977075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326701412335560144439969433 245026059251670108329977075)
      ·
        refine ⟨367539088877505162494965613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245026059251670108329977075 367539088877505162494965613)
        ·
          refine ⟨137827158329064435935612105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 367539088877505162494965613 137827158329064435935612105)
          ·
            refine ⟨103370368746798326951709079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137827158329064435935612105 103370368746798326951709079)
            ·
              refine ⟨155055553120197490427563619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103370368746798326951709079 155055553120197490427563619)
              ·
                refine ⟨232583329680296235641345429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155055553120197490427563619 232583329680296235641345429)
                ·
                  refine ⟨10902343578763886045688067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 232583329680296235641345429 10902343578763886045688067)
                  ·
                    refine ⟨16353515368145829068532101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10902343578763886045688067 16353515368145829068532101)
                    ·
                      refine ⟨3066284131527342950349769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16353515368145829068532101 3066284131527342950349769)
                      ·
                        rfl

theorem cell23_5971567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 6, 1, 4].length) (baseStart_5971567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5971567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5971567 prefixEnd_5971567 := by exact prefixLift 5971567
  have htrace : WordTrace (prefixWord ++ tailWord_5971567) baseStart_5971567 baseEnd_5971567 := by
    simpa [prefixWord, tailWord_5971567, baseEnd_5971567] using wordTrace_append hprefix tailTrace_5971567
  have hstable : (prefixWord ++ tailWord_5971567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5971567).length < 2 ^ (prefixWord ++ tailWord_5971567).sum := by decide
  have hdescent : baseEnd_5971567 < baseStart_5971567 := by decide
  rcases family_descends (prefixWord ++ tailWord_5971567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5971584 : List Nat := [2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 4]
def baseStart_5971584 : Nat := 118140960795 + 5971584 * 2 ^ 59
def prefixEnd_5971584 : Nat := 4983230072969 + 3 ^ 40 * 5971584 * 2
def baseEnd_5971584 : Nat := 3066292860698469383837191

theorem tailTrace_5971584 : CollatzResearch.WordTrace tailWord_5971584 prefixEnd_5971584 3066292860698469383837191 := by
  unfold tailWord_5971584
  simp only [CollatzResearch.WordTrace]
  refine ⟨108900780798989254098340903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145201041065319005464454537 108900780798989254098340903)
  ·
    refine ⟨163351171198483881147511355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108900780798989254098340903 163351171198483881147511355)
    ·
      refine ⟨245026756797725821721267033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163351171198483881147511355 245026756797725821721267033)
      ·
        refine ⟨183770067598294366290950275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245026756797725821721267033 183770067598294366290950275)
        ·
          refine ⟨275655101397441549436425413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183770067598294366290950275 275655101397441549436425413)
          ·
            refine ⟨51685331512020290519329765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 275655101397441549436425413 51685331512020290519329765)
            ·
              refine ⟨9690999658503804472374331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51685331512020290519329765 9690999658503804472374331)
              ·
                refine ⟨14536499487755706708561497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9690999658503804472374331 14536499487755706708561497)
                ·
                  refine ⟨10902374615816780031421123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14536499487755706708561497 10902374615816780031421123)
                  ·
                    refine ⟨16353561923725170047131685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10902374615816780031421123 16353561923725170047131685)
                    ·
                      refine ⟨3066292860698469383837191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16353561923725170047131685 3066292860698469383837191)
                      ·
                        rfl

theorem cell23_5971584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 4].length) (baseStart_5971584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5971584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5971584 prefixEnd_5971584 := by exact prefixLift 5971584
  have htrace : WordTrace (prefixWord ++ tailWord_5971584) baseStart_5971584 baseEnd_5971584 := by
    simpa [prefixWord, tailWord_5971584, baseEnd_5971584] using wordTrace_append hprefix tailTrace_5971584
  have hstable : (prefixWord ++ tailWord_5971584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5971584).length < 2 ^ (prefixWord ++ tailWord_5971584).sum := by decide
  have hdescent : baseEnd_5971584 < baseStart_5971584 := by decide
  rcases family_descends (prefixWord ++ tailWord_5971584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5971638 : List Nat := [5, 1, 3, 1, 1, 2, 1, 1, 1, 4, 3]
def baseStart_5971638 : Nat := 118140960795 + 5971638 * 2 ^ 59
def prefixEnd_5971638 : Nat := 4983230072969 + 3 ^ 40 * 5971638 * 2
def baseEnd_5971638 : Nat := 3066320588653812172561943

theorem tailTrace_5971638 : CollatzResearch.WordTrace tailWord_5971638 prefixEnd_5971638 3066320588653812172561943 := by
  unfold tailWord_5971638
  simp only [CollatzResearch.WordTrace]
  refine ⟨13612720696236429713696723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145202354093188583612765045 13612720696236429713696723)
  ·
    refine ⟨20419081044354644570545085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13612720696236429713696723 20419081044354644570545085)
    ·
      refine ⟨7657155391632991713954407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20419081044354644570545085 7657155391632991713954407)
      ·
        refine ⟨11485733087449487570931611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7657155391632991713954407 11485733087449487570931611)
        ·
          refine ⟨17228599631174231356397417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11485733087449487570931611 17228599631174231356397417)
          ·
            refine ⟨12921449723380673517298063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17228599631174231356397417 12921449723380673517298063)
            ·
              refine ⟨19382174585071010275947095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12921449723380673517298063 19382174585071010275947095)
              ·
                refine ⟨29073261877606515413920643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19382174585071010275947095 29073261877606515413920643)
                ·
                  refine ⟨43609892816409773120880965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29073261877606515413920643 43609892816409773120880965)
                  ·
                    refine ⟨8176854903076832460165181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43609892816409773120880965 8176854903076832460165181)
                    ·
                      refine ⟨3066320588653812172561943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8176854903076832460165181 3066320588653812172561943)
                      ·
                        rfl

theorem cell23_5971638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_5971638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5971638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5971638 prefixEnd_5971638 := by exact prefixLift 5971638
  have htrace : WordTrace (prefixWord ++ tailWord_5971638) baseStart_5971638 baseEnd_5971638 := by
    simpa [prefixWord, tailWord_5971638, baseEnd_5971638] using wordTrace_append hprefix tailTrace_5971638
  have hstable : (prefixWord ++ tailWord_5971638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5971638).length < 2 ^ (prefixWord ++ tailWord_5971638).sum := by decide
  have hdescent : baseEnd_5971638 < baseStart_5971638 := by decide
  rcases family_descends (prefixWord ++ tailWord_5971638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5971658 : List Nat := [3, 1, 2, 1, 6, 1, 1, 2, 6]
def baseStart_5971658 : Nat := 118140960795 + 5971658 * 2 ^ 59
def prefixEnd_5971658 : Nat := 4983230072969 + 3 ^ 40 * 5971658 * 2
def baseEnd_5971658 : Nat := 340703428696322454923539

theorem tailTrace_5971658 : CollatzResearch.WordTrace tailWord_5971658 prefixEnd_5971658 340703428696322454923539 := by
  unfold tailWord_5971658
  simp only [CollatzResearch.WordTrace]
  refine ⟨54451065149927604708718907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145202840399806945889917085 54451065149927604708718907)
  ·
    refine ⟨81676597724891407063078361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54451065149927604708718907 81676597724891407063078361)
    ·
      refine ⟨61257448293668555297308771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81676597724891407063078361 61257448293668555297308771)
      ·
        refine ⟨91886172440502832945963157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61257448293668555297308771 91886172440502832945963157)
        ·
          refine ⟨4307164333148570294342023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 91886172440502832945963157 4307164333148570294342023)
          ·
            refine ⟨6460746499722855441513035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4307164333148570294342023 6460746499722855441513035)
            ·
              refine ⟨9691119749584283162269553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6460746499722855441513035 9691119749584283162269553)
              ·
                refine ⟨7268339812188212371702165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9691119749584283162269553 7268339812188212371702165)
                ·
                  refine ⟨340703428696322454923539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7268339812188212371702165 340703428696322454923539)
                  ·
                    rfl

theorem cell23_5971658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 2, 6].length) (baseStart_5971658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5971658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5971658 prefixEnd_5971658 := by exact prefixLift 5971658
  have htrace : WordTrace (prefixWord ++ tailWord_5971658) baseStart_5971658 baseEnd_5971658 := by
    simpa [prefixWord, tailWord_5971658, baseEnd_5971658] using wordTrace_append hprefix tailTrace_5971658
  have hstable : (prefixWord ++ tailWord_5971658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5971658).length < 2 ^ (prefixWord ++ tailWord_5971658).sum := by decide
  have hdescent : baseEnd_5971658 < baseStart_5971658 := by decide
  rcases family_descends (prefixWord ++ tailWord_5971658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5971661 : List Nat := [1, 6, 2, 1, 1, 1, 1, 1, 1, 2, 6]
def baseStart_5971661 : Nat := 118140960795 + 5971661 * 2 ^ 59
def prefixEnd_5971661 : Nat := 4983230072969 + 3 ^ 40 * 5971661 * 2
def baseEnd_5971661 : Nat := 3066332398708865582574337

theorem tailTrace_5971661 : CollatzResearch.WordTrace tailWord_5971661 prefixEnd_5971661 3066332398708865582574337 := by
  unfold tailWord_5971661
  simp only [CollatzResearch.WordTrace]
  refine ⟨217804370018699550347234837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145202913345799700231489891 217804370018699550347234837)
  ·
    refine ⟨10209579844626541422526633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 217804370018699550347234837 10209579844626541422526633)
    ·
      refine ⟨7657184883469906066894975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10209579844626541422526633 7657184883469906066894975)
      ·
        refine ⟨11485777325204859100342463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7657184883469906066894975 11485777325204859100342463)
        ·
          refine ⟨17228665987807288650513695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11485777325204859100342463 17228665987807288650513695)
          ·
            refine ⟨25842998981710932975770543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17228665987807288650513695 25842998981710932975770543)
            ·
              refine ⟨38764498472566399463655815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25842998981710932975770543 38764498472566399463655815)
              ·
                refine ⟨58146747708849599195483723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38764498472566399463655815 58146747708849599195483723)
                ·
                  refine ⟨87220121563274398793225585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58146747708849599195483723 87220121563274398793225585)
                  ·
                    refine ⟨65415091172455799094919189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 87220121563274398793225585 65415091172455799094919189)
                    ·
                      refine ⟨3066332398708865582574337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65415091172455799094919189 3066332398708865582574337)
                      ·
                        rfl

theorem cell23_5971661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_5971661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5971661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5971661 prefixEnd_5971661 := by exact prefixLift 5971661
  have htrace : WordTrace (prefixWord ++ tailWord_5971661) baseStart_5971661 baseEnd_5971661 := by
    simpa [prefixWord, tailWord_5971661, baseEnd_5971661] using wordTrace_append hprefix tailTrace_5971661
  have hstable : (prefixWord ++ tailWord_5971661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5971661).length < 2 ^ (prefixWord ++ tailWord_5971661).sum := by decide
  have hdescent : baseEnd_5971661 < baseStart_5971661 := by decide
  rcases family_descends (prefixWord ++ tailWord_5971661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5971668 : List Nat := [2, 4, 1, 3, 1, 1, 1, 3, 3, 1, 3]
def baseStart_5971668 : Nat := 118140960795 + 5971668 * 2 ^ 59
def prefixEnd_5971668 : Nat := 4983230072969 + 3 ^ 40 * 5971668 * 2
def baseEnd_5971668 : Nat := 3066335993073447055186805

theorem tailTrace_5971668 : CollatzResearch.WordTrace tailWord_5971668 prefixEnd_5971668 3066335993073447055186805 := by
  unfold tailWord_5971668
  simp only [CollatzResearch.WordTrace]
  refine ⟨108902312664837095271369829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145203083553116127028493105 108902312664837095271369829)
  ·
    refine ⟨20419183624656955363381843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108902312664837095271369829 20419183624656955363381843)
    ·
      refine ⟨30628775436985433045072765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20419183624656955363381843 30628775436985433045072765)
      ·
        refine ⟨11485790788869537391902287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30628775436985433045072765 11485790788869537391902287)
        ·
          refine ⟨17228686183304306087853431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11485790788869537391902287 17228686183304306087853431)
          ·
            refine ⟨25843029274956459131780147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17228686183304306087853431 25843029274956459131780147)
            ·
              refine ⟨38764543912434688697670221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25843029274956459131780147 38764543912434688697670221)
              ·
                refine ⟨14536703967163008261626333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38764543912434688697670221 14536703967163008261626333)
                ·
                  refine ⟨5451263987686128098109875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14536703967163008261626333 5451263987686128098109875)
                  ·
                    refine ⟨8176895981529192147164813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5451263987686128098109875 8176895981529192147164813)
                    ·
                      refine ⟨3066335993073447055186805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8176895981529192147164813 3066335993073447055186805)
                      ·
                        rfl

theorem cell23_5971668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_5971668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5971668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5971668 prefixEnd_5971668 := by exact prefixLift 5971668
  have htrace : WordTrace (prefixWord ++ tailWord_5971668) baseStart_5971668 baseEnd_5971668 := by
    simpa [prefixWord, tailWord_5971668, baseEnd_5971668] using wordTrace_append hprefix tailTrace_5971668
  have hstable : (prefixWord ++ tailWord_5971668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5971668).length < 2 ^ (prefixWord ++ tailWord_5971668).sum := by decide
  have hdescent : baseEnd_5971668 < baseStart_5971668 := by decide
  rcases family_descends (prefixWord ++ tailWord_5971668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5971694 : List Nat := [4, 1, 2, 1, 1, 2, 1, 2, 3, 1, 5]
def baseStart_5971694 : Nat := 118140960795 + 5971694 * 2 ^ 59
def prefixEnd_5971694 : Nat := 4983230072969 + 3 ^ 40 * 5971694 * 2
def baseEnd_5971694 : Nat := 3066349343570463953461685

theorem tailTrace_5971694 : CollatzResearch.WordTrace tailWord_5971694 prefixEnd_5971694 3066349343570463953461685 := by
  unfold tailWord_5971694
  simp only [CollatzResearch.WordTrace]
  refine ⟨27225696703447499622898267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145203715751719997988790757 27225696703447499622898267)
  ·
    refine ⟨40838545055171249434347401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27225696703447499622898267 40838545055171249434347401)
    ·
      refine ⟨30628908791378437075760551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40838545055171249434347401 30628908791378437075760551)
      ·
        refine ⟨45943363187067655613640827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30628908791378437075760551 45943363187067655613640827)
        ·
          refine ⟨68915044780601483420461241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45943363187067655613640827 68915044780601483420461241)
          ·
            refine ⟨51686283585451112565345931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68915044780601483420461241 51686283585451112565345931)
            ·
              refine ⟨77529425378176668848018897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51686283585451112565345931 77529425378176668848018897)
              ·
                refine ⟨58147069033632501636014173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77529425378176668848018897 58147069033632501636014173)
                ·
                  refine ⟨21805150887612188113505315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58147069033632501636014173 21805150887612188113505315)
                  ·
                    refine ⟨32707726331418282170257973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21805150887612188113505315 32707726331418282170257973)
                    ·
                      refine ⟨3066349343570463953461685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32707726331418282170257973 3066349343570463953461685)
                      ·
                        rfl

theorem cell23_5971694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_5971694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5971694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5971694 prefixEnd_5971694 := by exact prefixLift 5971694
  have htrace : WordTrace (prefixWord ++ tailWord_5971694) baseStart_5971694 baseEnd_5971694 := by
    simpa [prefixWord, tailWord_5971694, baseEnd_5971694] using wordTrace_append hprefix tailTrace_5971694
  have hstable : (prefixWord ++ tailWord_5971694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5971694).length < 2 ^ (prefixWord ++ tailWord_5971694).sum := by decide
  have hdescent : baseEnd_5971694 < baseStart_5971694 := by decide
  rcases family_descends (prefixWord ++ tailWord_5971694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5971702 : List Nat := [5, 1, 1, 1, 1, 5, 1, 3, 1, 1, 3]
def baseStart_5971702 : Nat := 118140960795 + 5971702 * 2 ^ 59
def prefixEnd_5971702 : Nat := 4983230072969 + 3 ^ 40 * 5971702 * 2
def baseEnd_5971702 : Nat := 3066353451415699922161649

theorem tailTrace_5971702 : CollatzResearch.WordTrace tailWord_5971702 prefixEnd_5971702 3066353451415699922161649 := by
  unfold tailWord_5971702
  simp only [CollatzResearch.WordTrace]
  refine ⟨13612866588221938396842335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145203910274367342899651573 13612866588221938396842335)
  ·
    refine ⟨20419299882332907595263503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13612866588221938396842335 20419299882332907595263503)
    ·
      refine ⟨30628949823499361392895255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20419299882332907595263503 30628949823499361392895255)
      ·
        refine ⟨45943424735249042089342883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30628949823499361392895255 45943424735249042089342883)
        ·
          refine ⟨68915137102873563134014325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45943424735249042089342883 68915137102873563134014325)
          ·
            refine ⟨6460794103394396543813843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68915137102873563134014325 6460794103394396543813843)
            ·
              refine ⟨9691191155091594815720765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6460794103394396543813843 9691191155091594815720765)
              ·
                refine ⟨3634196683159348055895287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9691191155091594815720765 3634196683159348055895287)
                ·
                  refine ⟨5451295024739022083842931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3634196683159348055895287 5451295024739022083842931)
                  ·
                    refine ⟨8176942537108533125764397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5451295024739022083842931 8176942537108533125764397)
                    ·
                      refine ⟨3066353451415699922161649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8176942537108533125764397 3066353451415699922161649)
                      ·
                        rfl

theorem cell23_5971702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 3, 1, 1, 3].length) (baseStart_5971702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5971702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5971702 prefixEnd_5971702 := by exact prefixLift 5971702
  have htrace : WordTrace (prefixWord ++ tailWord_5971702) baseStart_5971702 baseEnd_5971702 := by
    simpa [prefixWord, tailWord_5971702, baseEnd_5971702] using wordTrace_append hprefix tailTrace_5971702
  have hstable : (prefixWord ++ tailWord_5971702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5971702).length < 2 ^ (prefixWord ++ tailWord_5971702).sum := by decide
  have hdescent : baseEnd_5971702 < baseStart_5971702 := by decide
  rcases family_descends (prefixWord ++ tailWord_5971702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5971711 : List Nat := [1, 1, 2, 2, 1, 3, 4, 3, 1, 2, 3]
def baseStart_5971711 : Nat := 118140960795 + 5971711 * 2 ^ 59
def prefixEnd_5971711 : Nat := 4983230072969 + 3 ^ 40 * 5971711 * 2
def baseEnd_5971711 : Nat := 3066358072741590386949107

theorem tailTrace_5971711 : CollatzResearch.WordTrace tailWord_5971711 prefixEnd_5971711 3066358072741590386949107 := by
  unfold tailWord_5971711
  simp only [CollatzResearch.WordTrace]
  refine ⟨217806193668518408886554987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145204129112345605924369991 217806193668518408886554987)
  ·
    refine ⟨326709290502777613329832481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217806193668518408886554987 326709290502777613329832481)
    ·
      refine ⟨245031967877083209997374361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326709290502777613329832481 245031967877083209997374361)
      ·
        refine ⟨183773975907812407498030771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245031967877083209997374361 183773975907812407498030771)
        ·
          refine ⟨275660963861718611247046157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183773975907812407498030771 275660963861718611247046157)
          ·
            refine ⟨103372861448144479217642309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 275660963861718611247046157 103372861448144479217642309)
            ·
              refine ⟨19382411521527089853307933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103372861448144479217642309 19382411521527089853307933)
              ·
                refine ⟨7268404320572658694990475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19382411521527089853307933 7268404320572658694990475)
                ·
                  refine ⟨10902606480858988042485713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7268404320572658694990475 10902606480858988042485713)
                  ·
                    refine ⟨8176954860644241031864285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10902606480858988042485713 8176954860644241031864285)
                    ·
                      refine ⟨3066358072741590386949107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8176954860644241031864285 3066358072741590386949107)
                      ·
                        rfl

theorem cell23_5971711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 3, 1, 2, 3].length) (baseStart_5971711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5971711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5971711 prefixEnd_5971711 := by exact prefixLift 5971711
  have htrace : WordTrace (prefixWord ++ tailWord_5971711) baseStart_5971711 baseEnd_5971711 := by
    simpa [prefixWord, tailWord_5971711, baseEnd_5971711] using wordTrace_append hprefix tailTrace_5971711
  have hstable : (prefixWord ++ tailWord_5971711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5971711).length < 2 ^ (prefixWord ++ tailWord_5971711).sum := by decide
  have hdescent : baseEnd_5971711 < baseStart_5971711 := by decide
  rcases family_descends (prefixWord ++ tailWord_5971711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5971735 : List Nat := [1, 1, 3, 4, 2, 3, 2, 1, 2, 4]
def baseStart_5971735 : Nat := 118140960795 + 5971735 * 2 ^ 59
def prefixEnd_5971735 : Nat := 4983230072969 + 3 ^ 40 * 5971735 * 2
def baseEnd_5971735 : Nat := 1022123465425766097682999

theorem tailTrace_5971735 : CollatzResearch.WordTrace tailWord_5971735 prefixEnd_5971735 1022123465425766097682999 := by
  unfold tailWord_5971735
  simp only [CollatzResearch.WordTrace]
  refine ⟨217807069020431460985428659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145204712680287640656952439 217807069020431460985428659)
  ·
    refine ⟨326710603530647191478142989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217807069020431460985428659 326710603530647191478142989)
    ·
      refine ⟨122516476323992696804303621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 326710603530647191478142989 122516476323992696804303621)
      ·
        refine ⟨22971839310748630650806929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122516476323992696804303621 22971839310748630650806929)
        ·
          refine ⟨17228879483061472988105197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22971839310748630650806929 17228879483061472988105197)
          ·
            refine ⟨6460829806148052370539449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17228879483061472988105197 6460829806148052370539449)
            ·
              refine ⟨4845622354611039277904587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6460829806148052370539449 4845622354611039277904587)
              ·
                refine ⟨7268433531916558916856881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4845622354611039277904587 7268433531916558916856881)
                ·
                  refine ⟨5451325148937419187642661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7268433531916558916856881 5451325148937419187642661)
                  ·
                    refine ⟨1022123465425766097682999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5451325148937419187642661 1022123465425766097682999)
                    ·
                      rfl

theorem cell23_5971735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2, 1, 2, 4].length) (baseStart_5971735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5971735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5971735 prefixEnd_5971735 := by exact prefixLift 5971735
  have htrace : WordTrace (prefixWord ++ tailWord_5971735) baseStart_5971735 baseEnd_5971735 := by
    simpa [prefixWord, tailWord_5971735, baseEnd_5971735] using wordTrace_append hprefix tailTrace_5971735
  have hstable : (prefixWord ++ tailWord_5971735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5971735).length < 2 ^ (prefixWord ++ tailWord_5971735).sum := by decide
  have hdescent : baseEnd_5971735 < baseStart_5971735 := by decide
  rcases family_descends (prefixWord ++ tailWord_5971735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5971775 : List Nat := [1, 1, 2, 2, 6, 1, 2, 2, 2, 1, 3]
def baseStart_5971775 : Nat := 118140960795 + 5971775 * 2 ^ 59
def prefixEnd_5971775 : Nat := 4983230072969 + 3 ^ 40 * 5971775 * 2
def baseEnd_5971775 : Nat := 3066390935503478136548813

theorem tailTrace_5971775 : CollatzResearch.WordTrace tailWord_5971775 prefixEnd_5971775 3066390935503478136548813 := by
  unfold tailWord_5971775
  simp only [CollatzResearch.WordTrace]
  refine ⟨217808527940286547816884779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145205685293524365211256519 217808527940286547816884779)
  ·
    refine ⟨326712791910429821725327169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217808527940286547816884779 326712791910429821725327169)
    ·
      refine ⟨245034593932822366293995377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326712791910429821725327169 245034593932822366293995377)
      ·
        refine ⟨183775945449616774720496533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245034593932822366293995377 183775945449616774720496533)
        ·
          refine ⟨8614497442950786315023275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 183775945449616774720496533 8614497442950786315023275)
          ·
            refine ⟨12921746164426179472534913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8614497442950786315023275 12921746164426179472534913)
            ·
              refine ⟨9691309623319634604401185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12921746164426179472534913 9691309623319634604401185)
              ·
                refine ⟨7268482217489725953300889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9691309623319634604401185 7268482217489725953300889)
                ·
                  refine ⟨5451361663117294464975667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7268482217489725953300889 5451361663117294464975667)
                  ·
                    refine ⟨8177042494675941697463501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5451361663117294464975667 8177042494675941697463501)
                    ·
                      refine ⟨3066390935503478136548813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8177042494675941697463501 3066390935503478136548813)
                      ·
                        rfl

theorem cell23_5971775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 2, 2, 1, 3].length) (baseStart_5971775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5971775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5971775 prefixEnd_5971775 := by exact prefixLift 5971775
  have htrace : WordTrace (prefixWord ++ tailWord_5971775) baseStart_5971775 baseEnd_5971775 := by
    simpa [prefixWord, tailWord_5971775, baseEnd_5971775] using wordTrace_append hprefix tailTrace_5971775
  have hstable : (prefixWord ++ tailWord_5971775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5971775).length < 2 ^ (prefixWord ++ tailWord_5971775).sum := by decide
  have hdescent : baseEnd_5971775 < baseStart_5971775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5971775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5971781 : List Nat := [1, 3, 1, 1, 1, 2, 3, 2, 3, 4, 2]
def baseStart_5971781 : Nat := 118140960795 + 5971781 * 2 ^ 59
def prefixEnd_5971781 : Nat := 4983230072969 + 3 ^ 40 * 5971781 * 2
def baseEnd_5971781 : Nat := 3066394016387405113073785

theorem tailTrace_5971781 : CollatzResearch.WordTrace tailWord_5971781 prefixEnd_5971781 3066394016387405113073785 := by
  unfold tailWord_5971781
  simp only [CollatzResearch.WordTrace]
  refine ⟨217808746778264810841603197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145205831185509873894402131 217808746778264810841603197)
  ·
    refine ⟨81678280041849304065601199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217808746778264810841603197 81678280041849304065601199)
    ·
      refine ⟨122517420062773956098401799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81678280041849304065601199 122517420062773956098401799)
      ·
        refine ⟨183776130094160934147602699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122517420062773956098401799 183776130094160934147602699)
        ·
          refine ⟨275664195141241401221404049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183776130094160934147602699 275664195141241401221404049)
          ·
            refine ⟨206748146355931050916053037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 275664195141241401221404049 206748146355931050916053037)
            ·
              refine ⟨77530554883474144093519889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 206748146355931050916053037 77530554883474144093519889)
              ·
                refine ⟨58147916162605608070139917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77530554883474144093519889 58147916162605608070139917)
                ·
                  refine ⟨21805468560977103026302469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58147916162605608070139917 21805468560977103026302469)
                  ·
                    refine ⟨4088525355183206817431713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21805468560977103026302469 4088525355183206817431713)
                    ·
                      refine ⟨3066394016387405113073785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4088525355183206817431713 3066394016387405113073785)
                      ·
                        rfl

theorem cell23_5971781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3, 4, 2].length) (baseStart_5971781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5971781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5971781 prefixEnd_5971781 := by exact prefixLift 5971781
  have htrace : WordTrace (prefixWord ++ tailWord_5971781) baseStart_5971781 baseEnd_5971781 := by
    simpa [prefixWord, tailWord_5971781, baseEnd_5971781] using wordTrace_append hprefix tailTrace_5971781
  have hstable : (prefixWord ++ tailWord_5971781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5971781).length < 2 ^ (prefixWord ++ tailWord_5971781).sum := by decide
  have hdescent : baseEnd_5971781 < baseStart_5971781 := by decide
  rcases family_descends (prefixWord ++ tailWord_5971781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5971838 : List Nat := [4, 2, 3, 1, 1, 1, 1, 3, 7]
def baseStart_5971838 : Nat := 118140960795 + 5971838 * 2 ^ 59
def prefixEnd_5971838 : Nat := 4983230072969 + 3 ^ 40 * 5971838 * 2
def baseEnd_5971838 : Nat := 340713698309412376673447

theorem tailTrace_5971838 : CollatzResearch.WordTrace tailWord_5971838 prefixEnd_5971838 340713698309412376673447 := by
  unfold tailWord_5971838
  simp only [CollatzResearch.WordTrace]
  refine ⟨27226353217382288697053521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145207217159372206384285445 27226353217382288697053521)
  ·
    refine ⟨20419764913036716522790141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27226353217382288697053521 20419764913036716522790141)
    ·
      refine ⟨7657411842388768696046303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20419764913036716522790141 7657411842388768696046303)
      ·
        refine ⟨11486117763583153044069455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7657411842388768696046303 11486117763583153044069455)
        ·
          refine ⟨17229176645374729566104183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11486117763583153044069455 17229176645374729566104183)
          ·
            refine ⟨25843764968062094349156275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17229176645374729566104183 25843764968062094349156275)
            ·
              refine ⟨38765647452093141523734413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25843764968062094349156275 38765647452093141523734413)
              ·
                refine ⟨14537117794534928071400405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38765647452093141523734413 14537117794534928071400405)
                ·
                  refine ⟨340713698309412376673447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14537117794534928071400405 340713698309412376673447)
                  ·
                    rfl

theorem cell23_5971838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 3, 7].length) (baseStart_5971838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5971838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5971838 prefixEnd_5971838 := by exact prefixLift 5971838
  have htrace : WordTrace (prefixWord ++ tailWord_5971838) baseStart_5971838 baseEnd_5971838 := by
    simpa [prefixWord, tailWord_5971838, baseEnd_5971838] using wordTrace_append hprefix tailTrace_5971838
  have hstable : (prefixWord ++ tailWord_5971838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5971838).length < 2 ^ (prefixWord ++ tailWord_5971838).sum := by decide
  have hdescent : baseEnd_5971838 < baseStart_5971838 := by decide
  rcases family_descends (prefixWord ++ tailWord_5971838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5971925 : List Nat := [1, 3, 2, 3, 2, 2, 2, 1, 2, 2, 3]
def baseStart_5971925 : Nat := 118140960795 + 5971925 * 2 ^ 59
def prefixEnd_5971925 : Nat := 4983230072969 + 3 ^ 40 * 5971925 * 2
def baseEnd_5971925 : Nat := 3066467957601652549673123

theorem tailTrace_5971925 : CollatzResearch.WordTrace tailWord_5971925 prefixEnd_5971925 3066467957601652549673123 := by
  unfold tailWord_5971925
  simp only [CollatzResearch.WordTrace]
  refine ⟨217813998889743123434845229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145209332593162082289896819 217813998889743123434845229)
  ·
    refine ⟨81680249583653671288066961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217813998889743123434845229 81680249583653671288066961)
    ·
      refine ⟨61260187187740253466050221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81680249583653671288066961 61260187187740253466050221)
      ·
        refine ⟨22972570195402595049768833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61260187187740253466050221 22972570195402595049768833)
        ·
          refine ⟨17229427646551946287326625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22972570195402595049768833 17229427646551946287326625)
          ·
            refine ⟨12922070734913959715494969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17229427646551946287326625 12922070734913959715494969)
            ·
              refine ⟨9691553051185469786621227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12922070734913959715494969 9691553051185469786621227)
              ·
                refine ⟨14537329576778204679931841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9691553051185469786621227 14537329576778204679931841)
                ·
                  refine ⟨10902997182583653509948881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14537329576778204679931841 10902997182583653509948881)
                  ·
                    refine ⟨8177247886937740132461661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10902997182583653509948881 8177247886937740132461661)
                    ·
                      refine ⟨3066467957601652549673123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8177247886937740132461661 3066467957601652549673123)
                      ·
                        rfl

theorem cell23_5971925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_5971925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5971925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5971925 prefixEnd_5971925 := by exact prefixLift 5971925
  have htrace : WordTrace (prefixWord ++ tailWord_5971925) baseStart_5971925 baseEnd_5971925 := by
    simpa [prefixWord, tailWord_5971925, baseEnd_5971925] using wordTrace_append hprefix tailTrace_5971925
  have hstable : (prefixWord ++ tailWord_5971925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5971925).length < 2 ^ (prefixWord ++ tailWord_5971925).sum := by decide
  have hdescent : baseEnd_5971925 < baseStart_5971925 := by decide
  rcases family_descends (prefixWord ++ tailWord_5971925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5971949 : List Nat := [1, 5, 1, 4, 1, 1, 1, 4, 1, 4]
def baseStart_5971949 : Nat := 118140960795 + 5971949 * 2 ^ 59
def prefixEnd_5971949 : Nat := 4983230072969 + 3 ^ 40 * 5971949 * 2
def baseEnd_5971949 : Nat := 1022160093712453485257671

theorem tailTrace_5971949 : CollatzResearch.WordTrace tailWord_5971949 prefixEnd_5971949 1022160093712453485257671 := by
  unfold tailWord_5971949
  simp only [CollatzResearch.WordTrace]
  refine ⟨217814874241656175533718901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145209916161104117022479267 217814874241656175533718901)
  ·
    refine ⟨20420144460155266456286147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 217814874241656175533718901 20420144460155266456286147)
    ·
      refine ⟨30630216690232899684429221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20420144460155266456286147 30630216690232899684429221)
      ·
        refine ⟨5743165629418668690830479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30630216690232899684429221 5743165629418668690830479)
        ·
          refine ⟨8614748444128003036245719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5743165629418668690830479 8614748444128003036245719)
          ·
            refine ⟨12922122666192004554368579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8614748444128003036245719 12922122666192004554368579)
            ·
              refine ⟨19383183999288006831552869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12922122666192004554368579 19383183999288006831552869)
              ·
                refine ⟨3634346999866501280916163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19383183999288006831552869 3634346999866501280916163)
                ·
                  refine ⟨5451520499799751921374245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3634346999866501280916163 5451520499799751921374245)
                  ·
                    refine ⟨1022160093712453485257671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5451520499799751921374245 1022160093712453485257671)
                    ·
                      rfl

theorem cell23_5971949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 4, 1, 4].length) (baseStart_5971949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5971949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5971949 prefixEnd_5971949 := by exact prefixLift 5971949
  have htrace : WordTrace (prefixWord ++ tailWord_5971949) baseStart_5971949 baseEnd_5971949 := by
    simpa [prefixWord, tailWord_5971949, baseEnd_5971949] using wordTrace_append hprefix tailTrace_5971949
  have hstable : (prefixWord ++ tailWord_5971949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5971949).length < 2 ^ (prefixWord ++ tailWord_5971949).sum := by decide
  have hdescent : baseEnd_5971949 < baseStart_5971949 := by decide
  rcases family_descends (prefixWord ++ tailWord_5971949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5971989 : List Nat := [1, 3, 2, 1, 5, 1, 2, 3, 1, 1, 3]
def baseStart_5971989 : Nat := 118140960795 + 5971989 * 2 ^ 59
def prefixEnd_5971989 : Nat := 4983230072969 + 3 ^ 40 * 5971989 * 2
def baseEnd_5971989 : Nat := 3066500820363540299272829

theorem tailTrace_5971989 : CollatzResearch.WordTrace tailWord_5971989 prefixEnd_5971989 3066500820363540299272829 := by
  unfold tailWord_5971989
  simp only [CollatzResearch.WordTrace]
  refine ⟨217816333161511262365175021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145210888774340841576783347 217816333161511262365175021)
  ·
    refine ⟨81681124935566723386940633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217816333161511262365175021 81681124935566723386940633)
    ·
      refine ⟨61260843701675042540205475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81681124935566723386940633 61260843701675042540205475)
      ·
        refine ⟨91891265552512563810308213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61260843701675042540205475 91891265552512563810308213)
        ·
          refine ⟨8614806145548052857216395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 91891265552512563810308213 8614806145548052857216395)
          ·
            refine ⟨12922209218322079285824593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8614806145548052857216395 12922209218322079285824593)
            ·
              refine ⟨9691656913741559464368445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12922209218322079285824593 9691656913741559464368445)
              ·
                refine ⟨3634371342653084799138167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9691656913741559464368445 3634371342653084799138167)
                ·
                  refine ⟨5451557013979627198707251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3634371342653084799138167 5451557013979627198707251)
                  ·
                    refine ⟨8177335520969440798060877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5451557013979627198707251 8177335520969440798060877)
                    ·
                      refine ⟨3066500820363540299272829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8177335520969440798060877 3066500820363540299272829)
                      ·
                        rfl

theorem cell23_5971989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 3, 1, 1, 3].length) (baseStart_5971989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5971989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5971989 prefixEnd_5971989 := by exact prefixLift 5971989
  have htrace : WordTrace (prefixWord ++ tailWord_5971989) baseStart_5971989 baseEnd_5971989 := by
    simpa [prefixWord, tailWord_5971989, baseEnd_5971989] using wordTrace_append hprefix tailTrace_5971989
  have hstable : (prefixWord ++ tailWord_5971989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5971989).length < 2 ^ (prefixWord ++ tailWord_5971989).sum := by decide
  have hdescent : baseEnd_5971989 < baseStart_5971989 := by decide
  rcases family_descends (prefixWord ++ tailWord_5971989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5972005 : List Nat := [1, 3, 1, 2, 2, 3, 3, 2, 2, 4]
def baseStart_5972005 : Nat := 118140960795 + 5972005 * 2 ^ 59
def prefixEnd_5972005 : Nat := 4983230072969 + 3 ^ 40 * 5972005 * 2
def baseEnd_5972005 : Nat := 1022169678684670745557585

theorem tailTrace_5972005 : CollatzResearch.WordTrace tailWord_5972005 prefixEnd_5972005 1022169678684670745557585 := by
  unfold tailWord_5972005
  simp only [CollatzResearch.WordTrace]
  refine ⟨217816916729453297097757469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145211277819635531398504979 217816916729453297097757469)
  ·
    refine ⟨81681343773544986411659051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217816916729453297097757469 81681343773544986411659051)
    ·
      refine ⟨122522015660317479617488577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81681343773544986411659051 122522015660317479617488577)
      ·
        refine ⟨91891511745238109713116433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122522015660317479617488577 91891511745238109713116433)
        ·
          refine ⟨68918633808928582284837325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91891511745238109713116433 68918633808928582284837325)
          ·
            refine ⟨25844487678348218356813997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68918633808928582284837325 25844487678348218356813997)
            ·
              refine ⟨9691682879380581883805249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25844487678348218356813997 9691682879380581883805249)
              ·
                refine ⟨7268762159535436412853937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9691682879380581883805249 7268762159535436412853937)
                ·
                  refine ⟨5451571619651577309640453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7268762159535436412853937 5451571619651577309640453)
                  ·
                    refine ⟨1022169678684670745557585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5451571619651577309640453 1022169678684670745557585)
                    ·
                      rfl

theorem cell23_5972005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 2, 2, 4].length) (baseStart_5972005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5972005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5972005 prefixEnd_5972005 := by exact prefixLift 5972005
  have htrace : WordTrace (prefixWord ++ tailWord_5972005) baseStart_5972005 baseEnd_5972005 := by
    simpa [prefixWord, tailWord_5972005, baseEnd_5972005] using wordTrace_append hprefix tailTrace_5972005
  have hstable : (prefixWord ++ tailWord_5972005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5972005).length < 2 ^ (prefixWord ++ tailWord_5972005).sum := by decide
  have hdescent : baseEnd_5972005 < baseStart_5972005 := by decide
  rcases family_descends (prefixWord ++ tailWord_5972005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5972031 : List Nat := [1, 1, 2, 2, 3, 1, 2, 2, 2, 7]
def baseStart_5972031 : Nat := 118140960795 + 5972031 * 2 ^ 59
def prefixEnd_5972031 : Nat := 4983230072969 + 3 ^ 40 * 5972031 * 2
def baseEnd_5972031 : Nat := 1022174128850343044982545

theorem tailTrace_5972031 : CollatzResearch.WordTrace tailWord_5972031 prefixEnd_5972031 1022174128850343044982545 := by
  unfold tailWord_5972031
  simp only [CollatzResearch.WordTrace]
  refine ⟨217817865027359103538203947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145211910018239402358802631 217817865027359103538203947)
  ·
    refine ⟨326726797541038655307305921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217817865027359103538203947 326726797541038655307305921)
    ·
      refine ⟨245045098155778991480479441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326726797541038655307305921 245045098155778991480479441)
      ·
        refine ⟨183783823616834243610359581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245045098155778991480479441 183783823616834243610359581)
        ·
          refine ⟨68918933856312841353884843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183783823616834243610359581 68918933856312841353884843)
          ·
            refine ⟨103378400784469262030827265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68918933856312841353884843 103378400784469262030827265)
            ·
              refine ⟨77533800588351946523120449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103378400784469262030827265 77533800588351946523120449)
              ·
                refine ⟨58150350441263959892340337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77533800588351946523120449 58150350441263959892340337)
                ·
                  refine ⟨43612762830947969919255253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58150350441263959892340337 43612762830947969919255253)
                  ·
                    refine ⟨1022174128850343044982545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43612762830947969919255253 1022174128850343044982545)
                    ·
                      rfl

theorem cell23_5972031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 7].length) (baseStart_5972031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5972031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5972031 prefixEnd_5972031 := by exact prefixLift 5972031
  have htrace : WordTrace (prefixWord ++ tailWord_5972031) baseStart_5972031 baseEnd_5972031 := by
    simpa [prefixWord, tailWord_5972031, baseEnd_5972031] using wordTrace_append hprefix tailTrace_5972031
  have hstable : (prefixWord ++ tailWord_5972031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5972031).length < 2 ^ (prefixWord ++ tailWord_5972031).sum := by decide
  have hdescent : baseEnd_5972031 < baseStart_5972031 := by decide
  rcases family_descends (prefixWord ++ tailWord_5972031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5972041 : List Nat := [1, 2, 1, 1, 2, 2, 3, 1, 1, 4, 5]
def baseStart_5972041 : Nat := 118140960795 + 5972041 * 2 ^ 59
def prefixEnd_5972041 : Nat := 4983230072969 + 3 ^ 40 * 5972041 * 2
def baseEnd_5972041 : Nat := 3066527521357574095822589

theorem tailTrace_5972041 : CollatzResearch.WordTrace tailWord_5972041 prefixEnd_5972041 3066527521357574095822589 := by
  unfold tailWord_5972041
  simp only [CollatzResearch.WordTrace]
  refine ⟨217818229757322875246067977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145212153171548583497378651 217818229757322875246067977)
  ·
    refine ⟨163363672317992156434550983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217818229757322875246067977 163363672317992156434550983)
    ·
      refine ⟨245045508476988234651826475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163363672317992156434550983 245045508476988234651826475)
      ·
        refine ⟨367568262715482351977739713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245045508476988234651826475 367568262715482351977739713)
        ·
          refine ⟨275676197036611763983304785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 367568262715482351977739713 275676197036611763983304785)
          ·
            refine ⟨206757147777458822987478589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 275676197036611763983304785 206757147777458822987478589)
            ·
              refine ⟨77533930416547058620304471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 206757147777458822987478589 77533930416547058620304471)
              ·
                refine ⟨116300895624820587930456707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77533930416547058620304471 116300895624820587930456707)
                ·
                  refine ⟨174451343437230881895685061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116300895624820587930456707 174451343437230881895685061)
                  ·
                    refine ⟨32709626894480790355440949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 174451343437230881895685061 32709626894480790355440949)
                    ·
                      refine ⟨3066527521357574095822589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32709626894480790355440949 3066527521357574095822589)
                      ·
                        rfl

theorem cell23_5972041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 4, 5].length) (baseStart_5972041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5972041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5972041 prefixEnd_5972041 := by exact prefixLift 5972041
  have htrace : WordTrace (prefixWord ++ tailWord_5972041) baseStart_5972041 baseEnd_5972041 := by
    simpa [prefixWord, tailWord_5972041, baseEnd_5972041] using wordTrace_append hprefix tailTrace_5972041
  have hstable : (prefixWord ++ tailWord_5972041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5972041).length < 2 ^ (prefixWord ++ tailWord_5972041).sum := by decide
  have hdescent : baseEnd_5972041 < baseStart_5972041 := by decide
  rcases family_descends (prefixWord ++ tailWord_5972041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5972045 : List Nat := [1, 6, 1, 1, 1, 1, 2, 1, 3, 3, 3]
def baseStart_5972045 : Nat := 118140960795 + 5972045 * 2 ^ 59
def prefixEnd_5972045 : Nat := 4983230072969 + 3 ^ 40 * 5972045 * 2
def baseEnd_5972045 : Nat := 3066529575280192080172571

theorem tailTrace_5972045 : CollatzResearch.WordTrace tailWord_5972045 prefixEnd_5972045 3066529575280192080172571 := by
  unfold tailWord_5972045
  simp only [CollatzResearch.WordTrace]
  refine ⟨217818375649308383929213589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145212250432872255952809059 217818375649308383929213589)
  ·
    refine ⟨10210236358561330496681887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 217818375649308383929213589 10210236358561330496681887)
    ·
      refine ⟨15315354537841995745022831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10210236358561330496681887 15315354537841995745022831)
      ·
        refine ⟨22973031806762993617534247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15315354537841995745022831 22973031806762993617534247)
        ·
          refine ⟨34459547710144490426301371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22973031806762993617534247 34459547710144490426301371)
          ·
            refine ⟨51689321565216735639452057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34459547710144490426301371 51689321565216735639452057)
            ·
              refine ⟨38766991173912551729589043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51689321565216735639452057 38766991173912551729589043)
              ·
                refine ⟨58150486760868827594383565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38766991173912551729589043 58150486760868827594383565)
                ·
                  refine ⟨21806432535325810347893837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58150486760868827594383565 21806432535325810347893837)
                  ·
                    refine ⟨8177412200747178880460189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21806432535325810347893837 8177412200747178880460189)
                    ·
                      refine ⟨3066529575280192080172571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8177412200747178880460189 3066529575280192080172571)
                      ·
                        rfl

theorem cell23_5972045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_5972045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5972045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5972045 prefixEnd_5972045 := by exact prefixLift 5972045
  have htrace : WordTrace (prefixWord ++ tailWord_5972045) baseStart_5972045 baseEnd_5972045 := by
    simpa [prefixWord, tailWord_5972045, baseEnd_5972045] using wordTrace_append hprefix tailTrace_5972045
  have hstable : (prefixWord ++ tailWord_5972045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5972045).length < 2 ^ (prefixWord ++ tailWord_5972045).sum := by decide
  have hdescent : baseEnd_5972045 < baseStart_5972045 := by decide
  rcases family_descends (prefixWord ++ tailWord_5972045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5972046 : List Nat := [4, 1, 1, 1, 1, 6, 1, 3, 1, 2, 2]
def baseStart_5972046 : Nat := 118140960795 + 5972046 * 2 ^ 59
def prefixEnd_5972046 : Nat := 4983230072969 + 3 ^ 40 * 5972046 * 2
def baseEnd_5972046 : Nat := 3066530088760846576260067

theorem tailTrace_5972046 : CollatzResearch.WordTrace tailWord_5972046 prefixEnd_5972046 3066530088760846576260067 := by
  unfold tailWord_5972046
  simp only [CollatzResearch.WordTrace]
  refine ⟨27227301515288095137499999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145212274748203174066666661 27227301515288095137499999)
  ·
    refine ⟨40840952272932142706249999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27227301515288095137499999 40840952272932142706249999)
    ·
      refine ⟨61261428409398214059374999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40840952272932142706249999 61261428409398214059374999)
      ·
        refine ⟨91892142614097321089062499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61261428409398214059374999 91892142614097321089062499)
        ·
          refine ⟨137838213921145981633593749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91892142614097321089062499 137838213921145981633593749)
          ·
            refine ⟨6461166277553717889074707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 137838213921145981633593749 6461166277553717889074707)
            ·
              refine ⟨9691749416330576833612061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6461166277553717889074707 9691749416330576833612061)
              ·
                refine ⟨3634406031123966312604523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9691749416330576833612061 3634406031123966312604523)
                ·
                  refine ⟨5451609046685949468906785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3634406031123966312604523 5451609046685949468906785)
                  ·
                    refine ⟨4088706785014462101680089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5451609046685949468906785 4088706785014462101680089)
                    ·
                      refine ⟨3066530088760846576260067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4088706785014462101680089 3066530088760846576260067)
                      ·
                        rfl

theorem cell23_5972046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 3, 1, 2, 2].length) (baseStart_5972046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5972046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5972046 prefixEnd_5972046 := by exact prefixLift 5972046
  have htrace : WordTrace (prefixWord ++ tailWord_5972046) baseStart_5972046 baseEnd_5972046 := by
    simpa [prefixWord, tailWord_5972046, baseEnd_5972046] using wordTrace_append hprefix tailTrace_5972046
  have hstable : (prefixWord ++ tailWord_5972046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5972046).length < 2 ^ (prefixWord ++ tailWord_5972046).sum := by decide
  have hdescent : baseEnd_5972046 < baseStart_5972046 := by decide
  rcases family_descends (prefixWord ++ tailWord_5972046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5972078 : List Nat := [4, 1, 2, 2, 1, 1, 2, 1, 1, 8]
def baseStart_5972078 : Nat := 118140960795 + 5972078 * 2 ^ 59
def prefixEnd_5972078 : Nat := 4983230072969 + 3 ^ 40 * 5972078 * 2
def baseEnd_5972078 : Nat := 1022182173380596817019973

theorem tailTrace_5972078 : CollatzResearch.WordTrace tailWord_5972078 prefixEnd_5972078 1022182173380596817019973 := by
  unfold tailWord_5972078
  simp only [CollatzResearch.WordTrace]
  refine ⟨27227447407273603820645611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145213052838792553710109925 27227447407273603820645611)
  ·
    refine ⟨40841171110910405730968417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27227447407273603820645611 40841171110910405730968417)
    ·
      refine ⟨30630878333182804298226313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40841171110910405730968417 30630878333182804298226313)
      ·
        refine ⟨22973158749887103223669735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30630878333182804298226313 22973158749887103223669735)
        ·
          refine ⟨34459738124830654835504603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22973158749887103223669735 34459738124830654835504603)
          ·
            refine ⟨51689607187245982253256905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34459738124830654835504603 51689607187245982253256905)
            ·
              refine ⟨38767205390434486689942679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51689607187245982253256905 38767205390434486689942679)
              ·
                refine ⟨58150808085651730034914019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38767205390434486689942679 58150808085651730034914019)
                ·
                  refine ⟨87226212128477595052371029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58150808085651730034914019 87226212128477595052371029)
                  ·
                    refine ⟨1022182173380596817019973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 87226212128477595052371029 1022182173380596817019973)
                    ·
                      rfl

theorem cell23_5972078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_5972078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5972078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5972078 prefixEnd_5972078 := by exact prefixLift 5972078
  have htrace : WordTrace (prefixWord ++ tailWord_5972078) baseStart_5972078 baseEnd_5972078 := by
    simpa [prefixWord, tailWord_5972078, baseEnd_5972078] using wordTrace_append hprefix tailTrace_5972078
  have hstable : (prefixWord ++ tailWord_5972078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5972078).length < 2 ^ (prefixWord ++ tailWord_5972078).sum := by decide
  have hdescent : baseEnd_5972078 < baseStart_5972078 := by decide
  rcases family_descends (prefixWord ++ tailWord_5972078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5972079 : List Nat := [1, 1, 2, 1, 3, 6, 2, 1, 2, 1, 3]
def baseStart_5972079 : Nat := 118140960795 + 5972079 * 2 ^ 59
def prefixEnd_5972079 : Nat := 4983230072969 + 3 ^ 40 * 5972079 * 2
def baseEnd_5972079 : Nat := 3066547033622444947147415

theorem tailTrace_5972079 : CollatzResearch.WordTrace tailWord_5972079 prefixEnd_5972079 3066547033622444947147415 := by
  unfold tailWord_5972079
  simp only [CollatzResearch.WordTrace]
  refine ⟨217819615731185207735951291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145213077154123471823967527 217819615731185207735951291)
  ·
    refine ⟨326729423596777811603926937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217819615731185207735951291 326729423596777811603926937)
    ·
      refine ⟨245047067697583358702945203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326729423596777811603926937 245047067697583358702945203)
      ·
        refine ⟨367570601546375038054417805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245047067697583358702945203 367570601546375038054417805)
        ·
          refine ⟨137838975579890639270406677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 367570601546375038054417805 137838975579890639270406677)
          ·
            refine ⟨6461201980307373715800313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 137838975579890639270406677 6461201980307373715800313)
            ·
              refine ⟨4845901485230530286850235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6461201980307373715800313 4845901485230530286850235)
              ·
                refine ⟨7268852227845795430275353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4845901485230530286850235 7268852227845795430275353)
                ·
                  refine ⟨5451639170884346572706515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7268852227845795430275353 5451639170884346572706515)
                  ·
                    refine ⟨8177458756326519859059773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5451639170884346572706515 8177458756326519859059773)
                    ·
                      refine ⟨3066547033622444947147415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8177458756326519859059773 3066547033622444947147415)
                      ·
                        rfl

theorem cell23_5972079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2, 1, 2, 1, 3].length) (baseStart_5972079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5972079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5972079 prefixEnd_5972079 := by exact prefixLift 5972079
  have htrace : WordTrace (prefixWord ++ tailWord_5972079) baseStart_5972079 baseEnd_5972079 := by
    simpa [prefixWord, tailWord_5972079, baseEnd_5972079] using wordTrace_append hprefix tailTrace_5972079
  have hstable : (prefixWord ++ tailWord_5972079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5972079).length < 2 ^ (prefixWord ++ tailWord_5972079).sum := by decide
  have hdescent : baseEnd_5972079 < baseStart_5972079 := by decide
  rcases family_descends (prefixWord ++ tailWord_5972079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5972089 : List Nat := [1, 2, 1, 3, 4, 3, 1, 2, 1, 3, 2]
def baseStart_5972089 : Nat := 118140960795 + 5972089 * 2 ^ 59
def prefixEnd_5972089 : Nat := 4983230072969 + 3 ^ 40 * 5972089 * 2
def baseEnd_5972089 : Nat := 3066552168428989908022369

theorem tailTrace_5972089 : CollatzResearch.WordTrace tailWord_5972089 prefixEnd_5972089 3066552168428989908022369 := by
  unfold tailWord_5972089
  simp only [CollatzResearch.WordTrace]
  refine ⟨217819980461148979443815321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145213320307432652962543547 217819980461148979443815321)
  ·
    refine ⟨163364985345861734582861491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217819980461148979443815321 163364985345861734582861491)
    ·
      refine ⟨245047478018792601874292237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163364985345861734582861491 245047478018792601874292237)
      ·
        refine ⟨91892804257047225702859589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 245047478018792601874292237 91892804257047225702859589)
        ·
          refine ⟨17229900798196354819286173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91892804257047225702859589 17229900798196354819286173)
          ·
            refine ⟨6461212799323633057232315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17229900798196354819286173 6461212799323633057232315)
            ·
              refine ⟨9691819198985449585848473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6461212799323633057232315 9691819198985449585848473)
              ·
                refine ⟨7268864399239087189386355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9691819198985449585848473 7268864399239087189386355)
                ·
                  refine ⟨10903296598858630784079533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7268864399239087189386355 10903296598858630784079533)
                  ·
                    refine ⟨4088736224571986544029825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10903296598858630784079533 4088736224571986544029825)
                    ·
                      refine ⟨3066552168428989908022369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4088736224571986544029825 3066552168428989908022369)
                      ·
                        rfl

theorem cell23_5972089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 2, 1, 3, 2].length) (baseStart_5972089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5972089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5972089 prefixEnd_5972089 := by exact prefixLift 5972089
  have htrace : WordTrace (prefixWord ++ tailWord_5972089) baseStart_5972089 baseEnd_5972089 := by
    simpa [prefixWord, tailWord_5972089, baseEnd_5972089] using wordTrace_append hprefix tailTrace_5972089
  have hstable : (prefixWord ++ tailWord_5972089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5972089).length < 2 ^ (prefixWord ++ tailWord_5972089).sum := by decide
  have hdescent : baseEnd_5972089 < baseStart_5972089 := by decide
  rcases family_descends (prefixWord ++ tailWord_5972089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5972175 : List Nat := [1, 1, 2, 1, 1, 3, 3, 1, 4, 4, 2]
def baseStart_5972175 : Nat := 118140960795 + 5972175 * 2 ^ 59
def prefixEnd_5972175 : Nat := 4983230072969 + 3 ^ 40 * 5972175 * 2
def baseEnd_5972175 : Nat := 3066596327765276571546973

theorem tailTrace_5972175 : CollatzResearch.WordTrace tailWord_5972175 prefixEnd_5972175 3066596327765276571546973 := by
  unfold tailWord_5972175
  simp only [CollatzResearch.WordTrace]
  refine ⟨217823117138837416131445979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145215411425891610754297319 217823117138837416131445979)
  ·
    refine ⟨326734675708256124197168969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217823117138837416131445979 326734675708256124197168969)
    ·
      refine ⟨245051006781192093147876727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326734675708256124197168969 245051006781192093147876727)
      ·
        refine ⟨367576510171788139721815091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245051006781192093147876727 367576510171788139721815091)
        ·
          refine ⟨551364765257682209582722637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367576510171788139721815091 551364765257682209582722637)
          ·
            refine ⟨206761786971630828593520989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 551364765257682209582722637 206761786971630828593520989)
            ·
              refine ⟨77535670114361560722570371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 206761786971630828593520989 77535670114361560722570371)
              ·
                refine ⟨116303505171542341083855557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77535670114361560722570371 116303505171542341083855557)
                ·
                  refine ⟨21806907219664188953222917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 116303505171542341083855557 21806907219664188953222917)
                  ·
                    refine ⟨4088795103687035428729297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21806907219664188953222917 4088795103687035428729297)
                    ·
                      refine ⟨3066596327765276571546973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4088795103687035428729297 3066596327765276571546973)
                      ·
                        rfl

theorem cell23_5972175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4, 4, 2].length) (baseStart_5972175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5972175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5972175 prefixEnd_5972175 := by exact prefixLift 5972175
  have htrace : WordTrace (prefixWord ++ tailWord_5972175) baseStart_5972175 baseEnd_5972175 := by
    simpa [prefixWord, tailWord_5972175, baseEnd_5972175] using wordTrace_append hprefix tailTrace_5972175
  have hstable : (prefixWord ++ tailWord_5972175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5972175).length < 2 ^ (prefixWord ++ tailWord_5972175).sum := by decide
  have hdescent : baseEnd_5972175 < baseStart_5972175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5972175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5972185 : List Nat := [1, 2, 1, 2, 3, 1, 3, 3, 3, 4]
def baseStart_5972185 : Nat := 118140960795 + 5972185 * 2 ^ 59
def prefixEnd_5972185 : Nat := 4983230072969 + 3 ^ 40 * 5972185 * 2
def baseEnd_5972185 : Nat := 1022200487523940510807309

theorem tailTrace_5972185 : CollatzResearch.WordTrace tailWord_5972185 prefixEnd_5972185 1022200487523940510807309 := by
  unfold tailWord_5972185
  simp only [CollatzResearch.WordTrace]
  refine ⟨217823481868801187839310009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145215654579200791892873339 217823481868801187839310009)
  ·
    refine ⟨163367611401600890879482507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217823481868801187839310009 163367611401600890879482507)
    ·
      refine ⟨245051417102401336319223761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163367611401600890879482507 245051417102401336319223761)
      ·
        refine ⟨183788562826801002239417821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245051417102401336319223761 183788562826801002239417821)
        ·
          refine ⟨68920711060050375839781683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183788562826801002239417821 68920711060050375839781683)
          ·
            refine ⟨103381066590075563759672525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68920711060050375839781683 103381066590075563759672525)
            ·
              refine ⟨38767899971278336409877197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103381066590075563759672525 38767899971278336409877197)
              ·
                refine ⟨14537962489229376153703949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38767899971278336409877197 14537962489229376153703949)
                ·
                  refine ⟨5451735933461016057638981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14537962489229376153703949 5451735933461016057638981)
                  ·
                    refine ⟨1022200487523940510807309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5451735933461016057638981 1022200487523940510807309)
                    ·
                      rfl

theorem cell23_5972185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3, 3, 4].length) (baseStart_5972185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5972185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5972185 prefixEnd_5972185 := by exact prefixLift 5972185
  have htrace : WordTrace (prefixWord ++ tailWord_5972185) baseStart_5972185 baseEnd_5972185 := by
    simpa [prefixWord, tailWord_5972185, baseEnd_5972185] using wordTrace_append hprefix tailTrace_5972185
  have hstable : (prefixWord ++ tailWord_5972185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5972185).length < 2 ^ (prefixWord ++ tailWord_5972185).sum := by decide
  have hdescent : baseEnd_5972185 < baseStart_5972185 := by decide
  rcases family_descends (prefixWord ++ tailWord_5972185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5972252 : List Nat := [2, 2, 3, 1, 1, 1, 1, 1, 6, 3, 2]
def baseStart_5972252 : Nat := 118140960795 + 5972252 * 2 ^ 59
def prefixEnd_5972252 : Nat := 4983230072969 + 3 ^ 40 * 5972252 * 2
def baseEnd_5972252 : Nat := 3066635865775672770284119

theorem tailTrace_5972252 : CollatzResearch.WordTrace tailWord_5972252 prefixEnd_5972252 3066635865775672770284119 := by
  unfold tailWord_5972252
  simp only [CollatzResearch.WordTrace]
  refine ⟨108912962779779229140999505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145217283706372305521332673 108912962779779229140999505)
  ·
    refine ⟨81684722084834421855749629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108912962779779229140999505 81684722084834421855749629)
    ·
      refine ⟨30631770781812908195906111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81684722084834421855749629 30631770781812908195906111)
      ·
        refine ⟨45947656172719362293859167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30631770781812908195906111 45947656172719362293859167)
        ·
          refine ⟨68921484259079043440788751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45947656172719362293859167 68921484259079043440788751)
          ·
            refine ⟨103382226388618565161183127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68921484259079043440788751 103382226388618565161183127)
            ·
              refine ⟨155073339582927847741774691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103382226388618565161183127 155073339582927847741774691)
              ·
                refine ⟨232610009374391771612662037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155073339582927847741774691 232610009374391771612662037)
                ·
                  refine ⟨10903594189424614294343533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 232610009374391771612662037 10903594189424614294343533)
                  ·
                    refine ⟨4088847821034230360378825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10903594189424614294343533 4088847821034230360378825)
                    ·
                      refine ⟨3066635865775672770284119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4088847821034230360378825 3066635865775672770284119)
                      ·
                        rfl

theorem cell23_5972252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 6, 3, 2].length) (baseStart_5972252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5972252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5972252 prefixEnd_5972252 := by exact prefixLift 5972252
  have htrace : WordTrace (prefixWord ++ tailWord_5972252) baseStart_5972252 baseEnd_5972252 := by
    simpa [prefixWord, tailWord_5972252, baseEnd_5972252] using wordTrace_append hprefix tailTrace_5972252
  have hstable : (prefixWord ++ tailWord_5972252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5972252).length < 2 ^ (prefixWord ++ tailWord_5972252).sum := by decide
  have hdescent : baseEnd_5972252 < baseStart_5972252 := by decide
  rcases family_descends (prefixWord ++ tailWord_5972252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5972263 : List Nat := [1, 1, 8, 1, 1, 1, 2, 1, 2, 2, 3]
def baseStart_5972263 : Nat := 118140960795 + 5972263 * 2 ^ 59
def prefixEnd_5972263 : Nat := 4983230072969 + 3 ^ 40 * 5972263 * 2
def baseEnd_5972263 : Nat := 3066641514062872227246569

theorem tailTrace_5972263 : CollatzResearch.WordTrace tailWord_5972263 prefixEnd_5972263 3066641514062872227246569 := by
  unfold tailWord_5972263
  simp only [CollatzResearch.WordTrace]
  refine ⟨217826326762518607160649443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145217551175012404773766295 217826326762518607160649443)
  ·
    refine ⟨326739490143777910740974165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217826326762518607160649443 326739490143777910740974165)
    ·
      refine ⟨3828978400122397391495791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 326739490143777910740974165 3828978400122397391495791)
      ·
        refine ⟨5743467600183596087243687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3828978400122397391495791 5743467600183596087243687)
        ·
          refine ⟨8615201400275394130865531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5743467600183596087243687 8615201400275394130865531)
          ·
            refine ⟨12922802100413091196298297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8615201400275394130865531 12922802100413091196298297)
            ·
              refine ⟨9692101575309818397223723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12922802100413091196298297 9692101575309818397223723)
              ·
                refine ⟨14538152362964727595835585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9692101575309818397223723 14538152362964727595835585)
                ·
                  refine ⟨10903614272223545696876689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14538152362964727595835585 10903614272223545696876689)
                  ·
                    refine ⟨8177710704167659272657517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10903614272223545696876689 8177710704167659272657517)
                    ·
                      refine ⟨3066641514062872227246569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8177710704167659272657517 3066641514062872227246569)
                      ·
                        rfl

theorem cell23_5972263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_5972263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5972263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5972263 prefixEnd_5972263 := by exact prefixLift 5972263
  have htrace : WordTrace (prefixWord ++ tailWord_5972263) baseStart_5972263 baseEnd_5972263 := by
    simpa [prefixWord, tailWord_5972263, baseEnd_5972263] using wordTrace_append hprefix tailTrace_5972263
  have hstable : (prefixWord ++ tailWord_5972263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5972263).length < 2 ^ (prefixWord ++ tailWord_5972263).sum := by decide
  have hdescent : baseEnd_5972263 < baseStart_5972263 := by decide
  rcases family_descends (prefixWord ++ tailWord_5972263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5972275 : List Nat := [1, 1, 1, 2, 5, 1, 3, 2, 1, 6]
def baseStart_5972275 : Nat := 118140960795 + 5972275 * 2 ^ 59
def prefixEnd_5972275 : Nat := 4983230072969 + 3 ^ 40 * 5972275 * 2
def baseEnd_5972275 : Nat := 1022215891943575393432171

theorem tailTrace_5972275 : CollatzResearch.WordTrace tailWord_5972275 prefixEnd_5972275 1022215891943575393432171 := by
  unfold tailWord_5972275
  simp only [CollatzResearch.WordTrace]
  refine ⟨217826764438475133210086279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145217842958983422140057519 217826764438475133210086279)
  ·
    refine ⟨326740146657712699815129419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217826764438475133210086279 326740146657712699815129419)
    ·
      refine ⟨490110219986569049722694129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326740146657712699815129419 490110219986569049722694129)
      ·
        refine ⟨367582664989926787292020597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 490110219986569049722694129 367582664989926787292020597)
        ·
          refine ⟨34460874842805636308626931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 367582664989926787292020597 34460874842805636308626931)
          ·
            refine ⟨51691312264208454462940397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34460874842805636308626931 51691312264208454462940397)
            ·
              refine ⟨19384242099078170423602649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51691312264208454462940397 19384242099078170423602649)
              ·
                refine ⟨14538181574308627817701987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19384242099078170423602649 14538181574308627817701987)
                ·
                  refine ⟨21807272361462941726552981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14538181574308627817701987 21807272361462941726552981)
                  ·
                    refine ⟨1022215891943575393432171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21807272361462941726552981 1022215891943575393432171)
                    ·
                      rfl

theorem cell23_5972275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 2, 1, 6].length) (baseStart_5972275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5972275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5972275 prefixEnd_5972275 := by exact prefixLift 5972275
  have htrace : WordTrace (prefixWord ++ tailWord_5972275) baseStart_5972275 baseEnd_5972275 := by
    simpa [prefixWord, tailWord_5972275, baseEnd_5972275] using wordTrace_append hprefix tailTrace_5972275
  have hstable : (prefixWord ++ tailWord_5972275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5972275).length < 2 ^ (prefixWord ++ tailWord_5972275).sum := by decide
  have hdescent : baseEnd_5972275 < baseStart_5972275 := by decide
  rcases family_descends (prefixWord ++ tailWord_5972275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5972295 : List Nat := [1, 1, 4, 1, 2, 2, 1, 2, 3, 2, 4]
def baseStart_5972295 : Nat := 118140960795 + 5972295 * 2 ^ 59
def prefixEnd_5972295 : Nat := 4983230072969 + 3 ^ 40 * 5972295 * 2
def baseEnd_5972295 : Nat := 3066657945443816102046421

theorem tailTrace_5972295 : CollatzResearch.WordTrace tailWord_5972295 prefixEnd_5972295 3066657945443816102046421 := by
  unfold tailWord_5972295
  simp only [CollatzResearch.WordTrace]
  refine ⟨217827493898402676625814339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145218329265601784417209559 217827493898402676625814339)
  ·
    refine ⟨326741240847604014938721509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217827493898402676625814339 326741240847604014938721509)
    ·
      refine ⟨61263982658925752801010283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 326741240847604014938721509 61263982658925752801010283)
      ·
        refine ⟨91895973988388629201515425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61263982658925752801010283 91895973988388629201515425)
        ·
          refine ⟨68921980491291471901136569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91895973988388629201515425 68921980491291471901136569)
          ·
            refine ⟨51691485368468603925852427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68921980491291471901136569 51691485368468603925852427)
            ·
              refine ⟨77537228052702905888778641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51691485368468603925852427 77537228052702905888778641)
              ·
                refine ⟨58152921039527179416583981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77537228052702905888778641 58152921039527179416583981)
                ·
                  refine ⟨21807345389822692281218993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58152921039527179416583981 21807345389822692281218993)
                  ·
                    refine ⟨16355509042367019210914245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21807345389822692281218993 16355509042367019210914245)
                    ·
                      refine ⟨3066657945443816102046421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16355509042367019210914245 3066657945443816102046421)
                      ·
                        rfl

theorem cell23_5972295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_5972295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5972295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5972295 prefixEnd_5972295 := by exact prefixLift 5972295
  have htrace : WordTrace (prefixWord ++ tailWord_5972295) baseStart_5972295 baseEnd_5972295 := by
    simpa [prefixWord, tailWord_5972295, baseEnd_5972295] using wordTrace_append hprefix tailTrace_5972295
  have hstable : (prefixWord ++ tailWord_5972295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5972295).length < 2 ^ (prefixWord ++ tailWord_5972295).sum := by decide
  have hdescent : baseEnd_5972295 < baseStart_5972295 := by decide
  rcases family_descends (prefixWord ++ tailWord_5972295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5972305 : List Nat := [1, 2, 2, 1, 4, 2, 3, 8]
def baseStart_5972305 : Nat := 118140960795 + 5972305 * 2 ^ 59
def prefixEnd_5972305 : Nat := 4983230072969 + 3 ^ 40 * 5972305 * 2
def baseEnd_5972305 : Nat := 113580114083346706034125

theorem tailTrace_5972305 : CollatzResearch.WordTrace tailWord_5972305 prefixEnd_5972305 113580114083346706034125 := by
  unfold tailWord_5972305
  simp only [CollatzResearch.WordTrace]
  refine ⟨217827858628366448333678369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145218572418910965555785579 217827858628366448333678369)
  ·
    refine ⟨163370893971274836250258777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217827858628366448333678369 163370893971274836250258777)
    ·
      refine ⟨122528170478456127187694083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163370893971274836250258777 122528170478456127187694083)
      ·
        refine ⟨183792255717684190781541125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122528170478456127187694083 183792255717684190781541125)
        ·
          refine ⟨34461047947065785771538961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 183792255717684190781541125 34461047947065785771538961)
          ·
            refine ⟨25845785960299339328654221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34461047947065785771538961 25845785960299339328654221)
            ·
              refine ⟨9692169735112252248245333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25845785960299339328654221 9692169735112252248245333)
              ·
                refine ⟨113580114083346706034125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9692169735112252248245333 113580114083346706034125)
                ·
                  rfl

theorem cell23_5972305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 8].length) (baseStart_5972305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5972305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5972305 prefixEnd_5972305 := by exact prefixLift 5972305
  have htrace : WordTrace (prefixWord ++ tailWord_5972305) baseStart_5972305 baseEnd_5972305 := by
    simpa [prefixWord, tailWord_5972305, baseEnd_5972305] using wordTrace_append hprefix tailTrace_5972305
  have hstable : (prefixWord ++ tailWord_5972305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5972305).length < 2 ^ (prefixWord ++ tailWord_5972305).sum := by decide
  have hdescent : baseEnd_5972305 < baseStart_5972305 := by decide
  rcases family_descends (prefixWord ++ tailWord_5972305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5972333 : List Nat := [1, 5, 1, 1, 1, 2, 4, 3, 1, 2, 2]
def baseStart_5972333 : Nat := 118140960795 + 5972333 * 2 ^ 59
def prefixEnd_5972333 : Nat := 4983230072969 + 3 ^ 40 * 5972333 * 2
def baseEnd_5972333 : Nat := 3066677457708686953371247

theorem tailTrace_5972333 : CollatzResearch.WordTrace tailWord_5972333 prefixEnd_5972333 3066677457708686953371247 := by
  unfold tailWord_5972333
  simp only [CollatzResearch.WordTrace]
  refine ⟨217828879872265009115697653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145219253248176672743798435 217828879872265009115697653)
  ·
    refine ⟨20421457488024844604596655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 217828879872265009115697653 20421457488024844604596655)
    ·
      refine ⟨30632186232037266906894983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20421457488024844604596655 30632186232037266906894983)
      ·
        refine ⟨45948279348055900360342475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30632186232037266906894983 45948279348055900360342475)
        ·
          refine ⟨68922419022083850540513713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45948279348055900360342475 68922419022083850540513713)
          ·
            refine ⟨51691814266562887905385285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68922419022083850540513713 51691814266562887905385285)
            ·
              refine ⟨9692215174980541482259741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51691814266562887905385285 9692215174980541482259741)
              ·
                refine ⟨3634580690617703055847403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9692215174980541482259741 3634580690617703055847403)
                ·
                  refine ⟨5451871035926554583771105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3634580690617703055847403 5451871035926554583771105)
                  ·
                    refine ⟨4088903276944915937828329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5451871035926554583771105 4088903276944915937828329)
                    ·
                      refine ⟨3066677457708686953371247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4088903276944915937828329 3066677457708686953371247)
                      ·
                        rfl

theorem cell23_5972333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 3, 1, 2, 2].length) (baseStart_5972333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5972333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5972333 prefixEnd_5972333 := by exact prefixLift 5972333
  have htrace : WordTrace (prefixWord ++ tailWord_5972333) baseStart_5972333 baseEnd_5972333 := by
    simpa [prefixWord, tailWord_5972333, baseEnd_5972333] using wordTrace_append hprefix tailTrace_5972333
  have hstable : (prefixWord ++ tailWord_5972333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5972333).length < 2 ^ (prefixWord ++ tailWord_5972333).sum := by decide
  have hdescent : baseEnd_5972333 < baseStart_5972333 := by decide
  rcases family_descends (prefixWord ++ tailWord_5972333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5972336 : List Nat := [2, 1, 1, 1, 4, 5, 2, 1, 1, 2, 3]
def baseStart_5972336 : Nat := 118140960795 + 5972336 * 2 ^ 59
def prefixEnd_5972336 : Nat := 4983230072969 + 3 ^ 40 * 5972336 * 2
def baseEnd_5972336 : Nat := 3066678998150650441633733

theorem tailTrace_5972336 : CollatzResearch.WordTrace tailWord_5972336 prefixEnd_5972336 3066678998150650441633733 := by
  unfold tailWord_5972336
  simp only [CollatzResearch.WordTrace]
  refine ⟨108914494645627070314028431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145219326194169427085371241 108914494645627070314028431)
  ·
    refine ⟨163371741968440605471042647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108914494645627070314028431 163371741968440605471042647)
    ·
      refine ⟨245057612952660908206563971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163371741968440605471042647 245057612952660908206563971)
      ·
        refine ⟨367586419428991362309845957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245057612952660908206563971 367586419428991362309845957)
        ·
          refine ⟨68922453642935880433096117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 367586419428991362309845957 68922453642935880433096117)
          ·
            refine ⟨6461480029025238790602761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68922453642935880433096117 6461480029025238790602761)
            ·
              refine ⟨4846110021768929092952071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6461480029025238790602761 4846110021768929092952071)
              ·
                refine ⟨7269165032653393639428107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4846110021768929092952071 7269165032653393639428107)
                ·
                  refine ⟨10903747548980090459142161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7269165032653393639428107 10903747548980090459142161)
                  ·
                    refine ⟨8177810661735067844356621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10903747548980090459142161 8177810661735067844356621)
                    ·
                      refine ⟨3066678998150650441633733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8177810661735067844356621 3066678998150650441633733)
                      ·
                        rfl

theorem cell23_5972336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2, 1, 1, 2, 3].length) (baseStart_5972336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5972336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5972336 prefixEnd_5972336 := by exact prefixLift 5972336
  have htrace : WordTrace (prefixWord ++ tailWord_5972336) baseStart_5972336 baseEnd_5972336 := by
    simpa [prefixWord, tailWord_5972336, baseEnd_5972336] using wordTrace_append hprefix tailTrace_5972336
  have hstable : (prefixWord ++ tailWord_5972336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5972336).length < 2 ^ (prefixWord ++ tailWord_5972336).sum := by decide
  have hdescent : baseEnd_5972336 < baseStart_5972336 := by decide
  rcases family_descends (prefixWord ++ tailWord_5972336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5972349 : List Nat := [1, 4, 1, 1, 2, 4, 1, 1, 4, 1, 3]
def baseStart_5972349 : Nat := 118140960795 + 5972349 * 2 ^ 59
def prefixEnd_5972349 : Nat := 4983230072969 + 3 ^ 40 * 5972349 * 2
def baseEnd_5972349 : Nat := 3066685673399158890771173

theorem tailTrace_5972349 : CollatzResearch.WordTrace tailWord_5972349 prefixEnd_5972349 3066685673399158890771173 := by
  unfold tailWord_5972349
  simp only [CollatzResearch.WordTrace]
  refine ⟨217829463440207043848280101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145219642293471362565520067 217829463440207043848280101)
  ·
    refine ⟨40843024395038820721552519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 217829463440207043848280101 40843024395038820721552519)
    ·
      refine ⟨61264536592558231082328779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40843024395038820721552519 61264536592558231082328779)
      ·
        refine ⟨91896804888837346623493169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61264536592558231082328779 91896804888837346623493169)
        ·
          refine ⟨68922603666628009967619877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91896804888837346623493169 68922603666628009967619877)
          ·
            refine ⟨12922988187492751868928727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68922603666628009967619877 12922988187492751868928727)
            ·
              refine ⟨19384482281239127803393091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12922988187492751868928727 19384482281239127803393091)
              ·
                refine ⟨29076723421858691705089637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19384482281239127803393091 29076723421858691705089637)
                ·
                  refine ⟨5451885641598504694704307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29076723421858691705089637 5451885641598504694704307)
                  ·
                    refine ⟨8177828462397757042056461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5451885641598504694704307 8177828462397757042056461)
                    ·
                      refine ⟨3066685673399158890771173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8177828462397757042056461 3066685673399158890771173)
                      ·
                        rfl

theorem cell23_5972349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 4, 1, 3].length) (baseStart_5972349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5972349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5972349 prefixEnd_5972349 := by exact prefixLift 5972349
  have htrace : WordTrace (prefixWord ++ tailWord_5972349) baseStart_5972349 baseEnd_5972349 := by
    simpa [prefixWord, tailWord_5972349, baseEnd_5972349] using wordTrace_append hprefix tailTrace_5972349
  have hstable : (prefixWord ++ tailWord_5972349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5972349).length < 2 ^ (prefixWord ++ tailWord_5972349).sum := by decide
  have hdescent : baseEnd_5972349 < baseStart_5972349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5972349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5972366 : List Nat := [4, 1, 1, 4, 1, 3, 1, 1, 1, 3, 3]
def baseStart_5972366 : Nat := 118140960795 + 5972366 * 2 ^ 59
def prefixEnd_5972366 : Nat := 4983230072969 + 3 ^ 40 * 5972366 * 2
def baseEnd_5972366 : Nat := 3066694402570285324258595

theorem tailTrace_5972366 : CollatzResearch.WordTrace tailWord_5972366 prefixEnd_5972366 3066694402570285324258595 := by
  unfold tailWord_5972366
  simp only [CollatzResearch.WordTrace]
  refine ⟨27228760435143181968956119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145220055654096970501099301 27228760435143181968956119)
  ·
    refine ⟨40843140652714772953434179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27228760435143181968956119 40843140652714772953434179)
    ·
      refine ⟨61264710979072159430151269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40843140652714772953434179 61264710979072159430151269)
      ·
        refine ⟨11487133308576029893153363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61264710979072159430151269 11487133308576029893153363)
        ·
          refine ⟨17230699962864044839730045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11487133308576029893153363 17230699962864044839730045)
          ·
            refine ⟨6461512486074016814898767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17230699962864044839730045 6461512486074016814898767)
            ·
              refine ⟨9692268729111025222348151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6461512486074016814898767 9692268729111025222348151)
              ·
                refine ⟨14538403093666537833522227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9692268729111025222348151 14538403093666537833522227)
                ·
                  refine ⟨21807604640499806750283341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14538403093666537833522227 21807604640499806750283341)
                  ·
                    refine ⟨8177851740187427531356253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21807604640499806750283341 8177851740187427531356253)
                    ·
                      refine ⟨3066694402570285324258595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8177851740187427531356253 3066694402570285324258595)
                      ·
                        rfl

theorem cell23_5972366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_5972366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5972366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5972366 prefixEnd_5972366 := by exact prefixLift 5972366
  have htrace : WordTrace (prefixWord ++ tailWord_5972366) baseStart_5972366 baseEnd_5972366 := by
    simpa [prefixWord, tailWord_5972366, baseEnd_5972366] using wordTrace_append hprefix tailTrace_5972366
  have hstable : (prefixWord ++ tailWord_5972366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5972366).length < 2 ^ (prefixWord ++ tailWord_5972366).sum := by decide
  have hdescent : baseEnd_5972366 < baseStart_5972366 := by decide
  rcases family_descends (prefixWord ++ tailWord_5972366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5972376 : List Nat := [2, 1, 2, 5, 1, 1, 1, 4, 1, 3, 2]
def baseStart_5972376 : Nat := 118140960795 + 5972376 * 2 ^ 59
def prefixEnd_5972376 : Nat := 4983230072969 + 3 ^ 40 * 5972376 * 2
def baseEnd_5972376 : Nat := 3066699537376830285133549

theorem tailTrace_5972376 : CollatzResearch.WordTrace tailWord_5972376 prefixEnd_5972376 3066699537376830285133549 := by
  unfold tailWord_5972376
  simp only [CollatzResearch.WordTrace]
  refine ⟨108915224105554613729756491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145220298807406151639675321 108915224105554613729756491)
  ·
    refine ⟨163372836158331920594634737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108915224105554613729756491 163372836158331920594634737)
    ·
      refine ⟨122529627118748940445976053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163372836158331920594634737 122529627118748940445976053)
      ·
        refine ⟨11487152542382713166810255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 122529627118748940445976053 11487152542382713166810255)
        ·
          refine ⟨17230728813574069750215383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11487152542382713166810255 17230728813574069750215383)
          ·
            refine ⟨25846093220361104625323075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17230728813574069750215383 25846093220361104625323075)
            ·
              refine ⟨38769139830541656937984613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25846093220361104625323075 38769139830541656937984613)
              ·
                refine ⟨7269213718226560675872115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38769139830541656937984613 7269213718226560675872115)
                ·
                  refine ⟨10903820577339841013808173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7269213718226560675872115 10903820577339841013808173)
                  ·
                    refine ⟨4088932716502440380178065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10903820577339841013808173 4088932716502440380178065)
                    ·
                      refine ⟨3066699537376830285133549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4088932716502440380178065 3066699537376830285133549)
                      ·
                        rfl

theorem cell23_5972376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_5972376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5972376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5972376 prefixEnd_5972376 := by exact prefixLift 5972376
  have htrace : WordTrace (prefixWord ++ tailWord_5972376) baseStart_5972376 baseEnd_5972376 := by
    simpa [prefixWord, tailWord_5972376, baseEnd_5972376] using wordTrace_append hprefix tailTrace_5972376
  have hstable : (prefixWord ++ tailWord_5972376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5972376).length < 2 ^ (prefixWord ++ tailWord_5972376).sum := by decide
  have hdescent : baseEnd_5972376 < baseStart_5972376 := by decide
  rcases family_descends (prefixWord ++ tailWord_5972376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5972389 : List Nat := [1, 3, 1, 2, 1, 1, 3, 1, 6, 2, 2]
def baseStart_5972389 : Nat := 118140960795 + 5972389 * 2 ^ 59
def prefixEnd_5972389 : Nat := 4983230072969 + 3 ^ 40 * 5972389 * 2
def baseEnd_5972389 : Nat := 3066706212625338734270989

theorem tailTrace_5972389 : CollatzResearch.WordTrace tailWord_5972389 prefixEnd_5972389 3066706212625338734270989 := by
  unfold tailWord_5972389
  simp only [CollatzResearch.WordTrace]
  refine ⟨217830922360062130679736221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145220614906708087119824147 217830922360062130679736221)
  ·
    refine ⟨81686595885023299004901083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217830922360062130679736221 81686595885023299004901083)
    ·
      refine ⟨122529893827534948507351625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81686595885023299004901083 122529893827534948507351625)
      ·
        refine ⟨91897420370651211380513719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122529893827534948507351625 91897420370651211380513719)
        ·
          refine ⟨137846130555976817070770579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91897420370651211380513719 137846130555976817070770579)
          ·
            refine ⟨206769195833965225606155869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137846130555976817070770579 206769195833965225606155869)
            ·
              refine ⟨77538448437736959602308451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 206769195833965225606155869 77538448437736959602308451)
              ·
                refine ⟨116307672656605439403462677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77538448437736959602308451 116307672656605439403462677)
                ·
                  refine ⟨5451922155778379972037313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 116307672656605439403462677 5451922155778379972037313)
                  ·
                    refine ⟨4088941616833784979027985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5451922155778379972037313 4088941616833784979027985)
                    ·
                      refine ⟨3066706212625338734270989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4088941616833784979027985 3066706212625338734270989)
                      ·
                        rfl

theorem cell23_5972389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 6, 2, 2].length) (baseStart_5972389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5972389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5972389 prefixEnd_5972389 := by exact prefixLift 5972389
  have htrace : WordTrace (prefixWord ++ tailWord_5972389) baseStart_5972389 baseEnd_5972389 := by
    simpa [prefixWord, tailWord_5972389, baseEnd_5972389] using wordTrace_append hprefix tailTrace_5972389
  have hstable : (prefixWord ++ tailWord_5972389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5972389).length < 2 ^ (prefixWord ++ tailWord_5972389).sum := by decide
  have hdescent : baseEnd_5972389 < baseStart_5972389 := by decide
  rcases family_descends (prefixWord ++ tailWord_5972389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5972423 : List Nat := [1, 1, 4, 1, 1, 4, 4, 1, 2, 2, 2]
def baseStart_5972423 : Nat := 118140960795 + 5972423 * 2 ^ 59
def prefixEnd_5972423 : Nat := 4983230072969 + 3 ^ 40 * 5972423 * 2
def baseEnd_5972423 : Nat := 3066723670967591601245833

theorem tailTrace_5972423 : CollatzResearch.WordTrace tailWord_5972423 prefixEnd_5972423 3066723670967591601245833 := by
  unfold tailWord_5972423
  simp only [CollatzResearch.WordTrace]
  refine ⟨217832162441938954486473923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145221441627959302990982615 217832162441938954486473923)
  ·
    refine ⟨326748243662908431729710885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217832162441938954486473923 326748243662908431729710885)
    ·
      refine ⟨61265295686795330949320791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 326748243662908431729710885 61265295686795330949320791)
      ·
        refine ⟨91897943530192996423981187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61265295686795330949320791 91897943530192996423981187)
        ·
          refine ⟨137846915295289494635971781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91897943530192996423981187 137846915295289494635971781)
          ·
            refine ⟨25846296617866780244244709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 137846915295289494635971781 25846296617866780244244709)
            ·
              refine ⟨4846180615850021295795883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25846296617866780244244709 4846180615850021295795883)
              ·
                refine ⟨7269270923775031943693825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4846180615850021295795883 7269270923775031943693825)
                ·
                  refine ⟨5451953192831273957770369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7269270923775031943693825 5451953192831273957770369)
                  ·
                    refine ⟨4088964894623455468327777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5451953192831273957770369 4088964894623455468327777)
                    ·
                      refine ⟨3066723670967591601245833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4088964894623455468327777 3066723670967591601245833)
                      ·
                        rfl

theorem cell23_5972423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4, 1, 2, 2, 2].length) (baseStart_5972423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5972423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5972423 prefixEnd_5972423 := by exact prefixLift 5972423
  have htrace : WordTrace (prefixWord ++ tailWord_5972423) baseStart_5972423 baseEnd_5972423 := by
    simpa [prefixWord, tailWord_5972423, baseEnd_5972423] using wordTrace_append hprefix tailTrace_5972423
  have hstable : (prefixWord ++ tailWord_5972423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5972423).length < 2 ^ (prefixWord ++ tailWord_5972423).sum := by decide
  have hdescent : baseEnd_5972423 < baseStart_5972423 := by decide
  rcases family_descends (prefixWord ++ tailWord_5972423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5972425 : List Nat := [1, 2, 1, 1, 2, 1, 4, 1, 3, 7]
def baseStart_5972425 : Nat := 118140960795 + 5972425 * 2 ^ 59
def prefixEnd_5972425 : Nat := 4983230072969 + 3 ^ 40 * 5972425 * 2
def baseEnd_5972425 : Nat := 1022241565976300197806941

theorem tailTrace_5972425 : CollatzResearch.WordTrace tailWord_5972425 prefixEnd_5972425 1022241565976300197806941 := by
  unfold tailWord_5972425
  simp only [CollatzResearch.WordTrace]
  refine ⟨217832235387931708828046729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145221490258621139218697819 217832235387931708828046729)
  ·
    refine ⟨163374176540948781621035047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217832235387931708828046729 163374176540948781621035047)
    ·
      refine ⟨245061264811423172431552571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163374176540948781621035047 245061264811423172431552571)
      ·
        refine ⟨367591897217134758647328857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245061264811423172431552571 367591897217134758647328857)
        ·
          refine ⟨275693922912851068985496643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 367591897217134758647328857 275693922912851068985496643)
          ·
            refine ⟨413540884369276603478244965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275693922912851068985496643 413540884369276603478244965)
            ·
              refine ⟨77538915819239363152170931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 413540884369276603478244965 77538915819239363152170931)
              ·
                refine ⟨116308373728859044728256397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77538915819239363152170931 116308373728859044728256397)
                ·
                  refine ⟨43615640148322141773096149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 116308373728859044728256397 43615640148322141773096149)
                  ·
                    refine ⟨1022241565976300197806941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43615640148322141773096149 1022241565976300197806941)
                    ·
                      rfl

theorem cell23_5972425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 7].length) (baseStart_5972425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5972425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5972425 prefixEnd_5972425 := by exact prefixLift 5972425
  have htrace : WordTrace (prefixWord ++ tailWord_5972425) baseStart_5972425 baseEnd_5972425 := by
    simpa [prefixWord, tailWord_5972425, baseEnd_5972425] using wordTrace_append hprefix tailTrace_5972425
  have hstable : (prefixWord ++ tailWord_5972425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5972425).length < 2 ^ (prefixWord ++ tailWord_5972425).sum := by decide
  have hdescent : baseEnd_5972425 < baseStart_5972425 := by decide
  rcases family_descends (prefixWord ++ tailWord_5972425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5972479 : List Nat := [1, 1, 2, 2, 1, 2, 5, 1, 2, 4, 2]
def baseStart_5972479 : Nat := 118140960795 + 5972479 * 2 ^ 59
def prefixEnd_5972479 : Nat := 4983230072969 + 3 ^ 40 * 5972479 * 2
def baseEnd_5972479 : Nat := 3066752425884243382145575

theorem tailTrace_5972479 : CollatzResearch.WordTrace tailWord_5972479 prefixEnd_5972479 3066752425884243382145575 := by
  unfold tailWord_5972479
  simp only [CollatzResearch.WordTrace]
  refine ⟨217834204929736076050512491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145222803286490717367008327 217834204929736076050512491)
  ·
    refine ⟨326751307394604114075768737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217834204929736076050512491 326751307394604114075768737)
    ·
      refine ⟨245063480545953085556826553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326751307394604114075768737 245063480545953085556826553)
      ·
        refine ⟨183797610409464814167619915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245063480545953085556826553 183797610409464814167619915)
        ·
          refine ⟨275696415614197221251429873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183797610409464814167619915 275696415614197221251429873)
          ·
            refine ⟨206772311710647915938572405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 275696415614197221251429873 206772311710647915938572405)
            ·
              refine ⟨19384904222873242119241163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 206772311710647915938572405 19384904222873242119241163)
              ·
                refine ⟨29077356334309863178861745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19384904222873242119241163 29077356334309863178861745)
                ·
                  refine ⟨21808017250732397384146309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29077356334309863178861745 21808017250732397384146309)
                  ·
                    refine ⟨4089003234512324509527433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21808017250732397384146309 4089003234512324509527433)
                    ·
                      refine ⟨3066752425884243382145575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4089003234512324509527433 3066752425884243382145575)
                      ·
                        rfl

theorem cell23_5972479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 2, 4, 2].length) (baseStart_5972479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5972479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5972479 prefixEnd_5972479 := by exact prefixLift 5972479
  have htrace : WordTrace (prefixWord ++ tailWord_5972479) baseStart_5972479 baseEnd_5972479 := by
    simpa [prefixWord, tailWord_5972479, baseEnd_5972479] using wordTrace_append hprefix tailTrace_5972479
  have hstable : (prefixWord ++ tailWord_5972479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5972479).length < 2 ^ (prefixWord ++ tailWord_5972479).sum := by decide
  have hdescent : baseEnd_5972479 < baseStart_5972479 := by decide
  rcases family_descends (prefixWord ++ tailWord_5972479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5972493 : List Nat := [1, 7, 1, 1, 1, 1, 3, 1, 2, 5]
def baseStart_5972493 : Nat := 118140960795 + 5972493 * 2 ^ 59
def prefixEnd_5972493 : Nat := 4983230072969 + 3 ^ 40 * 5972493 * 2
def baseEnd_5972493 : Nat := 1022253204871135442456837

theorem tailTrace_5972493 : CollatzResearch.WordTrace tailWord_5972493 prefixEnd_5972493 1022253204871135442456837 := by
  unfold tailWord_5972493
  simp only [CollatzResearch.WordTrace]
  refine ⟨217834715551685356441522133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145223143701123570961014755 217834715551685356441522133)
  ·
    refine ⟨5105501145742625541598175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 217834715551685356441522133 5105501145742625541598175)
    ·
      refine ⟨7658251718613938312397263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5105501145742625541598175 7658251718613938312397263)
      ·
        refine ⟨11487377577920907468595895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7658251718613938312397263 11487377577920907468595895)
        ·
          refine ⟨17231066366881361202893843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11487377577920907468595895 17231066366881361202893843)
          ·
            refine ⟨25846599550322041804340765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17231066366881361202893843 25846599550322041804340765)
            ·
              refine ⟨9692474831370765676627787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25846599550322041804340765 9692474831370765676627787)
              ·
                refine ⟨14538712247056148514941681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9692474831370765676627787 14538712247056148514941681)
                ·
                  refine ⟨10904034185292111386206261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14538712247056148514941681 10904034185292111386206261)
                  ·
                    refine ⟨1022253204871135442456837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10904034185292111386206261 1022253204871135442456837)
                    ·
                      rfl

theorem cell23_5972493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_5972493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5972493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5972493 prefixEnd_5972493 := by exact prefixLift 5972493
  have htrace : WordTrace (prefixWord ++ tailWord_5972493) baseStart_5972493 baseEnd_5972493 := by
    simpa [prefixWord, tailWord_5972493, baseEnd_5972493] using wordTrace_append hprefix tailTrace_5972493
  have hstable : (prefixWord ++ tailWord_5972493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5972493).length < 2 ^ (prefixWord ++ tailWord_5972493).sum := by decide
  have hdescent : baseEnd_5972493 < baseStart_5972493 := by decide
  rcases family_descends (prefixWord ++ tailWord_5972493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5972506 : List Nat := [3, 1, 1, 3, 1, 1, 3, 5, 1, 4]
def baseStart_5972506 : Nat := 118140960795 + 5972506 * 2 ^ 59
def prefixEnd_5972506 : Nat := 4983230072969 + 3 ^ 40 * 5972506 * 2
def baseEnd_5972506 : Nat := 1022255429953971592169317

theorem tailTrace_5972506 : CollatzResearch.WordTrace tailWord_5972506 prefixEnd_5972506 1022255429953971592169317 := by
  unfold tailWord_5972506
  simp only [CollatzResearch.WordTrace]
  refine ⟨54458797425159564915436343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145223459800425506441163581 54458797425159564915436343)
  ·
    refine ⟨81688196137739347373154515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54458797425159564915436343 81688196137739347373154515)
    ·
      refine ⟨122532294206609021059731773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81688196137739347373154515 122532294206609021059731773)
      ·
        refine ⟨45949610327478382897399415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122532294206609021059731773 45949610327478382897399415)
        ·
          refine ⟨68924415491217574346099123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45949610327478382897399415 68924415491217574346099123)
          ·
            refine ⟨103386623236826361519148685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68924415491217574346099123 103386623236826361519148685)
            ·
              refine ⟨38769983713809885569680757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103386623236826361519148685 38769983713809885569680757)
              ·
                refine ⟨3634685973169676772157571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38769983713809885569680757 3634685973169676772157571)
                ·
                  refine ⟨5452028959754515158236357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3634685973169676772157571 5452028959754515158236357)
                  ·
                    refine ⟨1022255429953971592169317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5452028959754515158236357 1022255429953971592169317)
                    ·
                      rfl

theorem cell23_5972506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 5, 1, 4].length) (baseStart_5972506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5972506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5972506 prefixEnd_5972506 := by exact prefixLift 5972506
  have htrace : WordTrace (prefixWord ++ tailWord_5972506) baseStart_5972506 baseEnd_5972506 := by
    simpa [prefixWord, tailWord_5972506, baseEnd_5972506] using wordTrace_append hprefix tailTrace_5972506
  have hstable : (prefixWord ++ tailWord_5972506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5972506).length < 2 ^ (prefixWord ++ tailWord_5972506).sum := by decide
  have hdescent : baseEnd_5972506 < baseStart_5972506 := by decide
  rcases family_descends (prefixWord ++ tailWord_5972506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5972549 : List Nat := [1, 3, 1, 1, 1, 5, 1, 4, 1, 5]
def baseStart_5972549 : Nat := 118140960795 + 5972549 * 2 ^ 59
def prefixEnd_5972549 : Nat := 4983230072969 + 3 ^ 40 * 5972549 * 2
def baseEnd_5972549 : Nat := 1022262789843352702756751

theorem tailTrace_5972549 : CollatzResearch.WordTrace tailWord_5972549 prefixEnd_5972549 1022262789843352702756751 := by
  unfold tailWord_5972549
  simp only [CollatzResearch.WordTrace]
  refine ⟨217836758039482478005560701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145224505359654985337040467 217836758039482478005560701)
  ·
    refine ⟨81688784264805929252085263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217836758039482478005560701 81688784264805929252085263)
    ·
      refine ⟨122533176397208893878127895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81688784264805929252085263 122533176397208893878127895)
      ·
        refine ⟨183799764595813340817191843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122533176397208893878127895 183799764595813340817191843)
        ·
          refine ⟨275699646893720011225787765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183799764595813340817191843 275699646893720011225787765)
          ·
            refine ⟨25846841896286251052417603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 275699646893720011225787765 25846841896286251052417603)
            ·
              refine ⟨38770262844429376578626405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25846841896286251052417603 38770262844429376578626405)
              ·
                refine ⟨7269424283330508108492451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38770262844429376578626405 7269424283330508108492451)
                ·
                  refine ⟨10904136424995762162738677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7269424283330508108492451 10904136424995762162738677)
                  ·
                    refine ⟨1022262789843352702756751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10904136424995762162738677 1022262789843352702756751)
                    ·
                      rfl

theorem cell23_5972549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 4, 1, 5].length) (baseStart_5972549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5972549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5972549 prefixEnd_5972549 := by exact prefixLift 5972549
  have htrace : WordTrace (prefixWord ++ tailWord_5972549) baseStart_5972549 baseEnd_5972549 := by
    simpa [prefixWord, tailWord_5972549, baseEnd_5972549] using wordTrace_append hprefix tailTrace_5972549
  have hstable : (prefixWord ++ tailWord_5972549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5972549).length < 2 ^ (prefixWord ++ tailWord_5972549).sum := by decide
  have hdescent : baseEnd_5972549 < baseStart_5972549 := by decide
  rcases family_descends (prefixWord ++ tailWord_5972549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5972552 : List Nat := [2, 1, 3, 1, 1, 1, 1, 2, 2, 5, 4]
def baseStart_5972552 : Nat := 118140960795 + 5972552 * 2 ^ 59
def prefixEnd_5972552 : Nat := 4983230072969 + 3 ^ 40 * 5972552 * 2
def baseEnd_5972552 : Nat := 3066789909972021596532739

theorem tailTrace_5972552 : CollatzResearch.WordTrace tailWord_5972552 prefixEnd_5972552 3066789909972021596532739 := by
  unfold tailWord_5972552
  simp only [CollatzResearch.WordTrace]
  refine ⟨108918433729235804758959955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145224578305647739678613273 108918433729235804758959955)
  ·
    refine ⟨163377650593853707138439933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108918433729235804758959955 163377650593853707138439933)
    ·
      refine ⟨61266618972695140176914975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163377650593853707138439933 61266618972695140176914975)
      ·
        refine ⟨91899928459042710265372463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61266618972695140176914975 91899928459042710265372463)
        ·
          refine ⟨137849892688564065398058695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91899928459042710265372463 137849892688564065398058695)
          ·
            refine ⟨206774839032846098097088043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137849892688564065398058695 206774839032846098097088043)
            ·
              refine ⟨310162258549269147145632065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206774839032846098097088043 310162258549269147145632065)
              ·
                refine ⟨232621693911951860359224049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 310162258549269147145632065 232621693911951860359224049)
                ·
                  refine ⟨174466270433963895269418037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 232621693911951860359224049 174466270433963895269418037)
                  ·
                    refine ⟨16356212853184115181507941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 174466270433963895269418037 16356212853184115181507941)
                    ·
                      refine ⟨3066789909972021596532739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16356212853184115181507941 3066789909972021596532739)
                      ·
                        rfl

theorem cell23_5972552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_5972552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5972552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5972552 prefixEnd_5972552 := by exact prefixLift 5972552
  have htrace : WordTrace (prefixWord ++ tailWord_5972552) baseStart_5972552 baseEnd_5972552 := by
    simpa [prefixWord, tailWord_5972552, baseEnd_5972552] using wordTrace_append hprefix tailTrace_5972552
  have hstable : (prefixWord ++ tailWord_5972552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5972552).length < 2 ^ (prefixWord ++ tailWord_5972552).sum := by decide
  have hdescent : baseEnd_5972552 < baseStart_5972552 := by decide
  rcases family_descends (prefixWord ++ tailWord_5972552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5972556 : List Nat := [2, 2, 1, 3, 1, 2, 2, 3, 2, 3, 2]
def baseStart_5972556 : Nat := 118140960795 + 5972556 * 2 ^ 59
def prefixEnd_5972556 : Nat := 4983230072969 + 3 ^ 40 * 5972556 * 2
def baseEnd_5972556 : Nat := 3066791963894639580882721

theorem tailTrace_5972556 : CollatzResearch.WordTrace tailWord_5972556 prefixEnd_5972556 3066791963894639580882721 := by
  unfold tailWord_5972556
  simp only [CollatzResearch.WordTrace]
  refine ⟨108918506675228559100532761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145224675566971412134043681 108918506675228559100532761)
  ·
    refine ⟨81688880006421419325399571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108918506675228559100532761 81688880006421419325399571)
    ·
      refine ⟨122533320009632128988099357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81688880006421419325399571 122533320009632128988099357)
      ·
        refine ⟨45949995003612048370537259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122533320009632128988099357 45949995003612048370537259)
        ·
          refine ⟨68924992505418072555805889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45949995003612048370537259 68924992505418072555805889)
          ·
            refine ⟨51693744379063554416854417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68924992505418072555805889 51693744379063554416854417)
            ·
              refine ⟨38770308284297665812640813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51693744379063554416854417 38770308284297665812640813)
              ·
                refine ⟨14538865606611624679740305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38770308284297665812640813 14538865606611624679740305)
                ·
                  refine ⟨10904149204958718509805229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14538865606611624679740305 10904149204958718509805229)
                  ·
                    refine ⟨4089055951859519441176961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10904149204958718509805229 4089055951859519441176961)
                    ·
                      refine ⟨3066791963894639580882721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4089055951859519441176961 3066791963894639580882721)
                      ·
                        rfl

theorem cell23_5972556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3, 2, 3, 2].length) (baseStart_5972556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5972556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5972556 prefixEnd_5972556 := by exact prefixLift 5972556
  have htrace : WordTrace (prefixWord ++ tailWord_5972556) baseStart_5972556 baseEnd_5972556 := by
    simpa [prefixWord, tailWord_5972556, baseEnd_5972556] using wordTrace_append hprefix tailTrace_5972556
  have hstable : (prefixWord ++ tailWord_5972556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5972556).length < 2 ^ (prefixWord ++ tailWord_5972556).sum := by decide
  have hdescent : baseEnd_5972556 < baseStart_5972556 := by decide
  rcases family_descends (prefixWord ++ tailWord_5972556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5972574 : List Nat := [4, 4, 1, 2, 2, 1, 1, 1, 3, 4]
def baseStart_5972574 : Nat := 118140960795 + 5972574 * 2 ^ 59
def prefixEnd_5972574 : Nat := 4983230072969 + 3 ^ 40 * 5972574 * 2
def baseEnd_5972574 : Nat := 1022267068848806836819213

theorem tailTrace_5972574 : CollatzResearch.WordTrace tailWord_5972574 prefixEnd_5972574 1022267068848806836819213 := by
  unfold tailWord_5972574
  simp only [CollatzResearch.WordTrace]
  refine ⟨27229708733048988409402597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145225113242927938183480517 27229708733048988409402597)
  ·
    refine ⟨5105570387446685326762987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27229708733048988409402597 5105570387446685326762987)
    ·
      refine ⟨7658355581170027990144481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5105570387446685326762987 7658355581170027990144481)
      ·
        refine ⟨5743766685877520992608361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7658355581170027990144481 5743766685877520992608361)
        ·
          refine ⟨4307825014408140744456271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5743766685877520992608361 4307825014408140744456271)
          ·
            refine ⟨6461737521612211116684407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4307825014408140744456271 6461737521612211116684407)
            ·
              refine ⟨9692606282418316675026611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6461737521612211116684407 9692606282418316675026611)
              ·
                refine ⟨14538909423627475012539917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9692606282418316675026611 14538909423627475012539917)
                ·
                  refine ⟨5452091033860303129702469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14538909423627475012539917 5452091033860303129702469)
                  ·
                    refine ⟨1022267068848806836819213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5452091033860303129702469 1022267068848806836819213)
                    ·
                      rfl

theorem cell23_5972574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_5972574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5972574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5972574 prefixEnd_5972574 := by exact prefixLift 5972574
  have htrace : WordTrace (prefixWord ++ tailWord_5972574) baseStart_5972574 baseEnd_5972574 := by
    simpa [prefixWord, tailWord_5972574, baseEnd_5972574] using wordTrace_append hprefix tailTrace_5972574
  have hstable : (prefixWord ++ tailWord_5972574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5972574).length < 2 ^ (prefixWord ++ tailWord_5972574).sum := by decide
  have hdescent : baseEnd_5972574 < baseStart_5972574 := by decide
  rcases family_descends (prefixWord ++ tailWord_5972574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5972579 : List Nat := [1, 1, 1, 5, 1, 2, 1, 3, 4, 4]
def baseStart_5972579 : Nat := 118140960795 + 5972579 * 2 ^ 59
def prefixEnd_5972579 : Nat := 4983230072969 + 3 ^ 40 * 5972579 * 2
def baseEnd_5972579 : Nat := 1022267924649897663631705

theorem tailTrace_5972579 : CollatzResearch.WordTrace tailWord_5972579 prefixEnd_5972579 1022267924649897663631705 := by
  unfold tailWord_5972579
  simp only [CollatzResearch.WordTrace]
  refine ⟨217837852229373793129152791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145225234819582528752768527 217837852229373793129152791)
  ·
    refine ⟨326756778344060689693729187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217837852229373793129152791 326756778344060689693729187)
    ·
      refine ⟨490135167516091034540593781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326756778344060689693729187 490135167516091034540593781)
      ·
        refine ⟨45950171954633534488180667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 490135167516091034540593781 45950171954633534488180667)
        ·
          refine ⟨68925257931950301732271001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45950171954633534488180667 68925257931950301732271001)
          ·
            refine ⟨51693943448962726299203251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68925257931950301732271001 51693943448962726299203251)
            ·
              refine ⟨77540915173444089448804877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51693943448962726299203251 77540915173444089448804877)
              ·
                refine ⟨29077843190041533543301829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77540915173444089448804877 29077843190041533543301829)
                ·
                  refine ⟨5452095598132787539369093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29077843190041533543301829 5452095598132787539369093)
                  ·
                    refine ⟨1022267924649897663631705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5452095598132787539369093 1022267924649897663631705)
                    ·
                      rfl

theorem cell23_5972579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 4, 4].length) (baseStart_5972579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5972579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5972579 prefixEnd_5972579 := by exact prefixLift 5972579
  have htrace : WordTrace (prefixWord ++ tailWord_5972579) baseStart_5972579 baseEnd_5972579 := by
    simpa [prefixWord, tailWord_5972579, baseEnd_5972579] using wordTrace_append hprefix tailTrace_5972579
  have hstable : (prefixWord ++ tailWord_5972579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5972579).length < 2 ^ (prefixWord ++ tailWord_5972579).sum := by decide
  have hdescent : baseEnd_5972579 < baseStart_5972579 := by decide
  rcases family_descends (prefixWord ++ tailWord_5972579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5972580 : List Nat := [2, 3, 1, 1, 2, 2, 5, 2, 1, 1, 3]
def baseStart_5972580 : Nat := 118140960795 + 5972580 * 2 ^ 59
def prefixEnd_5972580 : Nat := 4983230072969 + 3 ^ 40 * 5972580 * 2
def baseEnd_5972580 : Nat := 3066804287430347486982611

theorem tailTrace_5972580 : CollatzResearch.WordTrace tailWord_5972580 prefixEnd_5972580 3066804287430347486982611 := by
  unfold tailWord_5972580
  simp only [CollatzResearch.WordTrace]
  refine ⟨108918944351185085149969597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145225259134913446866626129 108918944351185085149969597)
  ·
    refine ⟨40844604131694406931238599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108918944351185085149969597 40844604131694406931238599)
    ·
      refine ⟨61266906197541610396857899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40844604131694406931238599 61266906197541610396857899)
      ·
        refine ⟨91900359296312415595286849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61266906197541610396857899 91900359296312415595286849)
        ·
          refine ⟨68925269472234311696465137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91900359296312415595286849 68925269472234311696465137)
          ·
            refine ⟨51693952104175733772348853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68925269472234311696465137 51693952104175733772348853)
            ·
              refine ⟨4846308009766475041157705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51693952104175733772348853 4846308009766475041157705)
              ·
                refine ⟨3634731007324856280868279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4846308009766475041157705 3634731007324856280868279)
                ·
                  refine ⟨5452096510987284421302419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3634731007324856280868279 5452096510987284421302419)
                  ·
                    refine ⟨8178144766480926631953629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5452096510987284421302419 8178144766480926631953629)
                    ·
                      refine ⟨3066804287430347486982611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8178144766480926631953629 3066804287430347486982611)
                      ·
                        rfl

theorem cell23_5972580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5, 2, 1, 1, 3].length) (baseStart_5972580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5972580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5972580 prefixEnd_5972580 := by exact prefixLift 5972580
  have htrace : WordTrace (prefixWord ++ tailWord_5972580) baseStart_5972580 baseEnd_5972580 := by
    simpa [prefixWord, tailWord_5972580, baseEnd_5972580] using wordTrace_append hprefix tailTrace_5972580
  have hstable : (prefixWord ++ tailWord_5972580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5972580).length < 2 ^ (prefixWord ++ tailWord_5972580).sum := by decide
  have hdescent : baseEnd_5972580 < baseStart_5972580 := by decide
  rcases family_descends (prefixWord ++ tailWord_5972580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5972637 : List Nat := [1, 4, 2, 1, 1, 1, 6, 2, 1, 2, 2]
def baseStart_5972637 : Nat := 118140960795 + 5972637 * 2 ^ 59
def prefixEnd_5972637 : Nat := 4983230072969 + 3 ^ 40 * 5972637 * 2
def baseEnd_5972637 : Nat := 3066833555827653763969849

theorem tailTrace_5972637 : CollatzResearch.WordTrace tailWord_5972637 prefixEnd_5972637 3066833555827653763969849 := by
  unfold tailWord_5972637
  simp only [CollatzResearch.WordTrace]
  refine ⟨217839967663163669034764165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145226645108775779356509443 217839967663163669034764165)
  ·
    refine ⟨40844993936843187944018281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 217839967663163669034764165 40844993936843187944018281)
    ·
      refine ⟨30633745452632390958013711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40844993936843187944018281 30633745452632390958013711)
      ·
        refine ⟨45950618178948586437020567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30633745452632390958013711 45950618178948586437020567)
        ·
          refine ⟨68925927268422879655530851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45950618178948586437020567 68925927268422879655530851)
          ·
            refine ⟨103388890902634319483296277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68925927268422879655530851 103388890902634319483296277)
            ·
              refine ⟨4846354261060983725779513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 103388890902634319483296277 4846354261060983725779513)
              ·
                refine ⟨3634765695795737794334635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4846354261060983725779513 3634765695795737794334635)
                ·
                  refine ⟨5452148543693606691501953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3634765695795737794334635 5452148543693606691501953)
                  ·
                    refine ⟨4089111407770205018626465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5452148543693606691501953 4089111407770205018626465)
                    ·
                      refine ⟨3066833555827653763969849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4089111407770205018626465 3066833555827653763969849)
                      ·
                        rfl

theorem cell23_5972637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6, 2, 1, 2, 2].length) (baseStart_5972637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5972637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5972637 prefixEnd_5972637 := by exact prefixLift 5972637
  have htrace : WordTrace (prefixWord ++ tailWord_5972637) baseStart_5972637 baseEnd_5972637 := by
    simpa [prefixWord, tailWord_5972637, baseEnd_5972637] using wordTrace_append hprefix tailTrace_5972637
  have hstable : (prefixWord ++ tailWord_5972637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5972637).length < 2 ^ (prefixWord ++ tailWord_5972637).sum := by decide
  have hdescent : baseEnd_5972637 < baseStart_5972637 := by decide
  rcases family_descends (prefixWord ++ tailWord_5972637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5972650 : List Nat := [3, 1, 5, 2, 1, 1, 2, 1, 1, 2, 4]
def baseStart_5972650 : Nat := 118140960795 + 5972650 * 2 ^ 59
def prefixEnd_5972650 : Nat := 4983230072969 + 3 ^ 40 * 5972650 * 2
def baseEnd_5972650 : Nat := 3066840231076162213107289

theorem tailTrace_5972650 : CollatzResearch.WordTrace tailWord_5972650 prefixEnd_5972650 3066840231076162213107289 := by
  unfold tailWord_5972650
  simp only [CollatzResearch.WordTrace]
  refine ⟨54460110453029143063746851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145226961208077714836658269 54460110453029143063746851)
  ·
    refine ⟨81690165679543714595620277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54460110453029143063746851 81690165679543714595620277)
    ·
      refine ⟨7658453032457223243339401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81690165679543714595620277 7658453032457223243339401)
      ·
        refine ⟨5743839774342917432504551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7658453032457223243339401 5743839774342917432504551)
        ·
          refine ⟨8615759661514376148756827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5743839774342917432504551 8615759661514376148756827)
          ·
            refine ⟨12923639492271564223135241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8615759661514376148756827 12923639492271564223135241)
            ·
              refine ⟨9692729619203673167351431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12923639492271564223135241 9692729619203673167351431)
              ·
                refine ⟨14539094428805509751027147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9692729619203673167351431 14539094428805509751027147)
                ·
                  refine ⟨21808641643208264626540721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14539094428805509751027147 21808641643208264626540721)
                  ·
                    refine ⟨16356481232406198469905541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21808641643208264626540721 16356481232406198469905541)
                    ·
                      refine ⟨3066840231076162213107289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16356481232406198469905541 3066840231076162213107289)
                      ·
                        rfl

theorem cell23_5972650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_5972650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5972650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5972650 prefixEnd_5972650 := by exact prefixLift 5972650
  have htrace : WordTrace (prefixWord ++ tailWord_5972650) baseStart_5972650 baseEnd_5972650 := by
    simpa [prefixWord, tailWord_5972650, baseEnd_5972650] using wordTrace_append hprefix tailTrace_5972650
  have hstable : (prefixWord ++ tailWord_5972650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5972650).length < 2 ^ (prefixWord ++ tailWord_5972650).sum := by decide
  have hdescent : baseEnd_5972650 < baseStart_5972650 := by decide
  rcases family_descends (prefixWord ++ tailWord_5972650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5972653 : List Nat := [1, 5, 2, 1, 1, 3, 2, 1, 1, 3, 3]
def baseStart_5972653 : Nat := 118140960795 + 5972653 * 2 ^ 59
def prefixEnd_5972653 : Nat := 4983230072969 + 3 ^ 40 * 5972653 * 2
def baseEnd_5972653 : Nat := 3066841771518125701369775

theorem tailTrace_5972653 : CollatzResearch.WordTrace tailWord_5972653 prefixEnd_5972653 3066841771518125701369775 := by
  unfold tailWord_5972653
  simp only [CollatzResearch.WordTrace]
  refine ⟨217840551231105703767346613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145227034154070469178231075 217840551231105703767346613)
  ·
    refine ⟨20422551677916159728188745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 217840551231105703767346613 20422551677916159728188745)
    ·
      refine ⟨15316913758437119796141559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20422551677916159728188745 15316913758437119796141559)
      ·
        refine ⟨22975370637655679694212339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15316913758437119796141559 22975370637655679694212339)
        ·
          refine ⟨34463055956483519541318509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22975370637655679694212339 34463055956483519541318509)
          ·
            refine ⟨12923645983681319827994441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34463055956483519541318509 12923645983681319827994441)
            ·
              refine ⟨9692734487760989870995831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12923645983681319827994441 9692734487760989870995831)
              ·
                refine ⟨14539101731641484806493747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9692734487760989870995831 14539101731641484806493747)
                ·
                  refine ⟨21808652597462227209740621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14539101731641484806493747 21808652597462227209740621)
                  ·
                    refine ⟨8178244724048335203652733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21808652597462227209740621 8178244724048335203652733)
                    ·
                      refine ⟨3066841771518125701369775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8178244724048335203652733 3066841771518125701369775)
                      ·
                        rfl

theorem cell23_5972653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_5972653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5972653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5972653 prefixEnd_5972653 := by exact prefixLift 5972653
  have htrace : WordTrace (prefixWord ++ tailWord_5972653) baseStart_5972653 baseEnd_5972653 := by
    simpa [prefixWord, tailWord_5972653, baseEnd_5972653] using wordTrace_append hprefix tailTrace_5972653
  have hstable : (prefixWord ++ tailWord_5972653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5972653).length < 2 ^ (prefixWord ++ tailWord_5972653).sum := by decide
  have hdescent : baseEnd_5972653 < baseStart_5972653 := by decide
  rcases family_descends (prefixWord ++ tailWord_5972653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5972679 : List Nat := [1, 1, 4, 1, 1, 1, 2, 2, 1, 6, 3]
def baseStart_5972679 : Nat := 118140960795 + 5972679 * 2 ^ 59
def prefixEnd_5972679 : Nat := 4983230072969 + 3 ^ 40 * 5972679 * 2
def baseEnd_5972679 : Nat := 3066855122015142599644655

theorem tailTrace_5972679 : CollatzResearch.WordTrace tailWord_5972679 prefixEnd_5972679 3066855122015142599644655 := by
  unfold tailWord_5972679
  simp only [CollatzResearch.WordTrace]
  refine ⟨217841499529011510207793091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145227666352674340138528727 217841499529011510207793091)
  ·
    refine ⟨326762249293517265311689637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217841499529011510207793091 326762249293517265311689637)
    ·
      refine ⟨61267921742534487245941807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 326762249293517265311689637 61267921742534487245941807)
      ·
        refine ⟨91901882613801730868912711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61267921742534487245941807 91901882613801730868912711)
        ·
          refine ⟨137852823920702596303369067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91901882613801730868912711 137852823920702596303369067)
          ·
            refine ⟨206779235881053894455053601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137852823920702596303369067 206779235881053894455053601)
            ·
              refine ⟨155084426910790420841290201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 206779235881053894455053601 155084426910790420841290201)
              ·
                refine ⟨116313320183092815630967651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155084426910790420841290201 116313320183092815630967651)
                ·
                  refine ⟨174469980274639223446451477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116313320183092815630967651 174469980274639223446451477)
                  ·
                    refine ⟨8178280325373713599052413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 174469980274639223446451477 8178280325373713599052413)
                    ·
                      refine ⟨3066855122015142599644655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8178280325373713599052413 3066855122015142599644655)
                      ·
                        rfl

theorem cell23_5972679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 6, 3].length) (baseStart_5972679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5972679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5972679 prefixEnd_5972679 := by exact prefixLift 5972679
  have htrace : WordTrace (prefixWord ++ tailWord_5972679) baseStart_5972679 baseEnd_5972679 := by
    simpa [prefixWord, tailWord_5972679, baseEnd_5972679] using wordTrace_append hprefix tailTrace_5972679
  have hstable : (prefixWord ++ tailWord_5972679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5972679).length < 2 ^ (prefixWord ++ tailWord_5972679).sum := by decide
  have hdescent : baseEnd_5972679 < baseStart_5972679 := by decide
  rcases family_descends (prefixWord ++ tailWord_5972679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5972680 : List Nat := [2, 1, 3, 1, 2, 3, 4, 1, 1, 3, 2]
def baseStart_5972680 : Nat := 118140960795 + 5972680 * 2 ^ 59
def prefixEnd_5972680 : Nat := 4983230072969 + 3 ^ 40 * 5972680 * 2
def baseEnd_5972680 : Nat := 3066855635495797095732151

theorem tailTrace_5972680 : CollatzResearch.WordTrace tailWord_5972680 prefixEnd_5972680 3066855635495797095732151 := by
  unfold tailWord_5972680
  simp only [CollatzResearch.WordTrace]
  refine ⟨108920768001003943689289747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145227690668005258252386329 108920768001003943689289747)
  ·
    refine ⟨163381152001505915533934621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108920768001003943689289747 163381152001505915533934621)
    ·
      refine ⟨61267932000564718325225483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163381152001505915533934621 61267932000564718325225483)
      ·
        refine ⟨91901898000847077487838225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61267932000564718325225483 91901898000847077487838225)
        ·
          refine ⟨68926423500635308115878669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91901898000847077487838225 68926423500635308115878669)
          ·
            refine ⟨25847408812738240543454501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68926423500635308115878669 25847408812738240543454501)
            ·
              refine ⟨4846389152388420101897719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25847408812738240543454501 4846389152388420101897719)
              ·
                refine ⟨7269583728582630152846579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4846389152388420101897719 7269583728582630152846579)
                ·
                  refine ⟨10904375592873945229269869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7269583728582630152846579 10904375592873945229269869)
                  ·
                    refine ⟨4089140847327729460976201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10904375592873945229269869 4089140847327729460976201)
                    ·
                      refine ⟨3066855635495797095732151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4089140847327729460976201 3066855635495797095732151)
                      ·
                        rfl

theorem cell23_5972680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4, 1, 1, 3, 2].length) (baseStart_5972680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5972680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5972680 prefixEnd_5972680 := by exact prefixLift 5972680
  have htrace : WordTrace (prefixWord ++ tailWord_5972680) baseStart_5972680 baseEnd_5972680 := by
    simpa [prefixWord, tailWord_5972680, baseEnd_5972680] using wordTrace_append hprefix tailTrace_5972680
  have hstable : (prefixWord ++ tailWord_5972680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5972680).length < 2 ^ (prefixWord ++ tailWord_5972680).sum := by decide
  have hdescent : baseEnd_5972680 < baseStart_5972680 := by decide
  rcases family_descends (prefixWord ++ tailWord_5972680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5972689 : List Nat := [1, 2, 2, 1, 2, 3, 1, 1, 4, 2, 4]
def baseStart_5972689 : Nat := 118140960795 + 5972689 * 2 ^ 59
def prefixEnd_5972689 : Nat := 4983230072969 + 3 ^ 40 * 5972689 * 2
def baseEnd_5972689 : Nat := 3066860256821687560519609

theorem tailTrace_5972689 : CollatzResearch.WordTrace tailWord_5972689 prefixEnd_5972689 3066860256821687560519609 := by
  unfold tailWord_5972689
  simp only [CollatzResearch.WordTrace]
  refine ⟨217841864258975281915657121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145227909505983521277104747 217841864258975281915657121)
  ·
    refine ⟨163381398194231461436742841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217841864258975281915657121 163381398194231461436742841)
    ·
      refine ⟨122536048645673596077557131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163381398194231461436742841 122536048645673596077557131)
      ·
        refine ⟨183804072968510394116335697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122536048645673596077557131 183804072968510394116335697)
        ·
          refine ⟨137853054726382795587251773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183804072968510394116335697 137853054726382795587251773)
          ·
            refine ⟨51694895522393548345219415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137853054726382795587251773 51694895522393548345219415)
            ·
              refine ⟨77542343283590322517829123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51694895522393548345219415 77542343283590322517829123)
              ·
                refine ⟨116313514925385483776743685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77542343283590322517829123 116313514925385483776743685)
                ·
                  refine ⟨21808784048509778208139441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 116313514925385483776743685 21808784048509778208139441)
                  ·
                    refine ⟨16356588036382333656104581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21808784048509778208139441 16356588036382333656104581)
                    ·
                      refine ⟨3066860256821687560519609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16356588036382333656104581 3066860256821687560519609)
                      ·
                        rfl

theorem cell23_5972689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 4, 2, 4].length) (baseStart_5972689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5972689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5972689 prefixEnd_5972689 := by exact prefixLift 5972689
  have htrace : WordTrace (prefixWord ++ tailWord_5972689) baseStart_5972689 baseEnd_5972689 := by
    simpa [prefixWord, tailWord_5972689, baseEnd_5972689] using wordTrace_append hprefix tailTrace_5972689
  have hstable : (prefixWord ++ tailWord_5972689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5972689).length < 2 ^ (prefixWord ++ tailWord_5972689).sum := by decide
  have hdescent : baseEnd_5972689 < baseStart_5972689 := by decide
  rcases family_descends (prefixWord ++ tailWord_5972689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5972729 : List Nat := [1, 2, 1, 3, 1, 1, 1, 2, 6, 5]
def baseStart_5972729 : Nat := 118140960795 + 5972729 * 2 ^ 59
def prefixEnd_5972729 : Nat := 4983230072969 + 3 ^ 40 * 5972729 * 2
def baseEnd_5972729 : Nat := 1022293598682622468006475

theorem tailTrace_5972729 : CollatzResearch.WordTrace tailWord_5972729 prefixEnd_5972729 1022293598682622468006475 := by
  unfold tailWord_5972729
  simp only [CollatzResearch.WordTrace]
  refine ⟨217843323178830368747113241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145228882119220245831408827 217843323178830368747113241)
  ·
    refine ⟨163382492384122776560334931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217843323178830368747113241 163382492384122776560334931)
    ·
      refine ⟨245073738576184164840502397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163382492384122776560334931 245073738576184164840502397)
      ·
        refine ⟨91902651966069061815188399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 245073738576184164840502397 91902651966069061815188399)
        ·
          refine ⟨137853977949103592722782599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91902651966069061815188399 137853977949103592722782599)
          ·
            refine ⟨206780966923655389084173899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137853977949103592722782599 206780966923655389084173899)
            ·
              refine ⟨310171450385483083626260849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206780966923655389084173899 310171450385483083626260849)
              ·
                refine ⟨232628587789112312719695637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 310171450385483083626260849 232628587789112312719695637)
                ·
                  refine ⟨10904465052614639658735733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 232628587789112312719695637 10904465052614639658735733)
                  ·
                    refine ⟨1022293598682622468006475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10904465052614639658735733 1022293598682622468006475)
                    ·
                      rfl

theorem cell23_5972729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 6, 5].length) (baseStart_5972729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5972729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5972729 prefixEnd_5972729 := by exact prefixLift 5972729
  have htrace : WordTrace (prefixWord ++ tailWord_5972729) baseStart_5972729 baseEnd_5972729 := by
    simpa [prefixWord, tailWord_5972729, baseEnd_5972729] using wordTrace_append hprefix tailTrace_5972729
  have hstable : (prefixWord ++ tailWord_5972729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5972729).length < 2 ^ (prefixWord ++ tailWord_5972729).sum := by decide
  have hdescent : baseEnd_5972729 < baseStart_5972729 := by decide
  rcases family_descends (prefixWord ++ tailWord_5972729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5972739 : List Nat := [1, 1, 1, 3, 2, 2, 1, 4, 1, 2, 5]
def baseStart_5972739 : Nat := 118140960795 + 5972739 * 2 ^ 59
def prefixEnd_5972739 : Nat := 4983230072969 + 3 ^ 40 * 5972739 * 2
def baseEnd_5972739 : Nat := 3066885930854412364894379

theorem tailTrace_5972739 : CollatzResearch.WordTrace tailWord_5972739 prefixEnd_5972739 3066885930854412364894379 := by
  unfold tailWord_5972739
  simp only [CollatzResearch.WordTrace]
  refine ⟨217843687908794140454977271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145229125272529426969984847 217843687908794140454977271)
  ·
    refine ⟨326765531863191210682465907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217843687908794140454977271 326765531863191210682465907)
    ·
      refine ⟨490148297794786816023698861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326765531863191210682465907 490148297794786816023698861)
      ·
        refine ⟨183805611673045056008887073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 490148297794786816023698861 183805611673045056008887073)
        ·
          refine ⟨137854208754783792006665305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183805611673045056008887073 137854208754783792006665305)
          ·
            refine ⟨103390656566087844004998979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137854208754783792006665305 103390656566087844004998979)
            ·
              refine ⟨155085984849131766007498469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103390656566087844004998979 155085984849131766007498469)
              ·
                refine ⟨29078622159212206126405963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 155085984849131766007498469 29078622159212206126405963)
                ·
                  refine ⟨43617933238818309189608945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29078622159212206126405963 43617933238818309189608945)
                  ·
                    refine ⟨32713449929113731892206709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43617933238818309189608945 32713449929113731892206709)
                    ·
                      refine ⟨3066885930854412364894379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32713449929113731892206709 3066885930854412364894379)
                      ·
                        rfl

theorem cell23_5972739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 2, 5].length) (baseStart_5972739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5972739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5972739 prefixEnd_5972739 := by exact prefixLift 5972739
  have htrace : WordTrace (prefixWord ++ tailWord_5972739) baseStart_5972739 baseEnd_5972739 := by
    simpa [prefixWord, tailWord_5972739, baseEnd_5972739] using wordTrace_append hprefix tailTrace_5972739
  have hstable : (prefixWord ++ tailWord_5972739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5972739).length < 2 ^ (prefixWord ++ tailWord_5972739).sum := by decide
  have hdescent : baseEnd_5972739 < baseStart_5972739 := by decide
  rcases family_descends (prefixWord ++ tailWord_5972739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5972746 : List Nat := [3, 1, 2, 2, 1, 2, 3, 2, 2, 5]
def baseStart_5972746 : Nat := 118140960795 + 5972746 * 2 ^ 59
def prefixEnd_5972746 : Nat := 4983230072969 + 3 ^ 40 * 5972746 * 2
def baseEnd_5972746 : Nat := 1022296508406331279168949

theorem tailTrace_5972746 : CollatzResearch.WordTrace tailWord_5972746 prefixEnd_5972746 1022296508406331279168949 := by
  unfold tailWord_5972746
  simp only [CollatzResearch.WordTrace]
  refine ⟨54460985804942195162620523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145229295479845853766988061 54460985804942195162620523)
  ·
    refine ⟨81691478707413292743930785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54460985804942195162620523 81691478707413292743930785)
    ·
      refine ⟨61268609030559969557948089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81691478707413292743930785 61268609030559969557948089)
      ·
        refine ⟨45951456772919977168461067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61268609030559969557948089 45951456772919977168461067)
        ·
          refine ⟨68927185159379965752691601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45951456772919977168461067 68927185159379965752691601)
          ·
            refine ⟨51695388869534974314518701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68927185159379965752691601 51695388869534974314518701)
            ·
              refine ⟨19385770826075615367944513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51695388869534974314518701 19385770826075615367944513)
              ·
                refine ⟨14539328119556711525958385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19385770826075615367944513 14539328119556711525958385)
                ·
                  refine ⟨10904496089667533644468789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14539328119556711525958385 10904496089667533644468789)
                  ·
                    refine ⟨1022296508406331279168949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10904496089667533644468789 1022296508406331279168949)
                    ·
                      rfl

theorem cell23_5972746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 2, 2, 5].length) (baseStart_5972746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5972746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5972746 prefixEnd_5972746 := by exact prefixLift 5972746
  have htrace : WordTrace (prefixWord ++ tailWord_5972746) baseStart_5972746 baseEnd_5972746 := by
    simpa [prefixWord, tailWord_5972746, baseEnd_5972746] using wordTrace_append hprefix tailTrace_5972746
  have hstable : (prefixWord ++ tailWord_5972746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5972746).length < 2 ^ (prefixWord ++ tailWord_5972746).sum := by decide
  have hdescent : baseEnd_5972746 < baseStart_5972746 := by decide
  rcases family_descends (prefixWord ++ tailWord_5972746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5972779 : List Nat := [1, 1, 1, 1, 2, 1, 2, 3, 1, 6, 4]
def baseStart_5972779 : Nat := 118140960795 + 5972779 * 2 ^ 59
def prefixEnd_5972779 : Nat := 4983230072969 + 3 ^ 40 * 5972779 * 2
def baseEnd_5972779 : Nat := 3066906470080592208394195

theorem tailTrace_5972779 : CollatzResearch.WordTrace tailWord_5972779 prefixEnd_5972779 3066906470080592208394195 := by
  unfold tailWord_5972779
  simp only [CollatzResearch.WordTrace]
  refine ⟨217845146828649227286433391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145230097885766151524288927 217845146828649227286433391)
  ·
    refine ⟨326767720242973840929650087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217845146828649227286433391 326767720242973840929650087)
    ·
      refine ⟨490151580364460761394475131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326767720242973840929650087 490151580364460761394475131)
      ·
        refine ⟨735227370546691142091712697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 490151580364460761394475131 735227370546691142091712697)
        ·
          refine ⟨551420527910018356568784523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 735227370546691142091712697 551420527910018356568784523)
          ·
            refine ⟨827130791865027534853176785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 551420527910018356568784523 827130791865027534853176785)
            ·
              refine ⟨620348093898770651139882589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 827130791865027534853176785 620348093898770651139882589)
              ·
                refine ⟨232630535212038994177455971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 620348093898770651139882589 232630535212038994177455971)
                ·
                  refine ⟨348945802818058491266183957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 232630535212038994177455971 348945802818058491266183957)
                  ·
                    refine ⟨16356834507096491778102373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 348945802818058491266183957 16356834507096491778102373)
                    ·
                      refine ⟨3066906470080592208394195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16356834507096491778102373 3066906470080592208394195)
                      ·
                        rfl

theorem cell23_5972779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 6, 4].length) (baseStart_5972779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5972779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5972779 prefixEnd_5972779 := by exact prefixLift 5972779
  have htrace : WordTrace (prefixWord ++ tailWord_5972779) baseStart_5972779 baseEnd_5972779 := by
    simpa [prefixWord, tailWord_5972779, baseEnd_5972779] using wordTrace_append hprefix tailTrace_5972779
  have hstable : (prefixWord ++ tailWord_5972779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5972779).length < 2 ^ (prefixWord ++ tailWord_5972779).sum := by decide
  have hdescent : baseEnd_5972779 < baseStart_5972779 := by decide
  rcases family_descends (prefixWord ++ tailWord_5972779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5972856 : List Nat := [2, 1, 2, 1, 1, 1, 1, 4, 5, 1, 4]
def baseStart_5972856 : Nat := 118140960795 + 5972856 * 2 ^ 59
def prefixEnd_5972856 : Nat := 4983230072969 + 3 ^ 40 * 5972856 * 2
def baseEnd_5972856 : Nat := 3066946008090988407131341

theorem tailTrace_5972856 : CollatzResearch.WordTrace tailWord_5972856 prefixEnd_5972856 3066946008090988407131341 := by
  unfold tailWord_5972856
  simp only [CollatzResearch.WordTrace]
  refine ⟨108923977624685134718493211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145231970166246846291324281 108923977624685134718493211)
  ·
    refine ⟨163385966437027702077739817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108923977624685134718493211 163385966437027702077739817)
    ·
      refine ⟨122539474827770776558304863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163385966437027702077739817 122539474827770776558304863)
      ·
        refine ⟨183809212241656164837457295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122539474827770776558304863 183809212241656164837457295)
        ·
          refine ⟨275713818362484247256185943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183809212241656164837457295 275713818362484247256185943)
          ·
            refine ⟨413570727543726370884278915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275713818362484247256185943 413570727543726370884278915)
            ·
              refine ⟨620356091315589556326418373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 413570727543726370884278915 620356091315589556326418373)
              ·
                refine ⟨116316767121673041811203445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 620356091315589556326418373 116316767121673041811203445)
                ·
                  refine ⟨10904696917656847669800323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 116316767121673041811203445 10904696917656847669800323)
                  ·
                    refine ⟨16357045376485271504700485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10904696917656847669800323 16357045376485271504700485)
                    ·
                      refine ⟨3066946008090988407131341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16357045376485271504700485 3066946008090988407131341)
                      ·
                        rfl

theorem cell23_5972856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 5, 1, 4].length) (baseStart_5972856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5972856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5972856 prefixEnd_5972856 := by exact prefixLift 5972856
  have htrace : WordTrace (prefixWord ++ tailWord_5972856) baseStart_5972856 baseEnd_5972856 := by
    simpa [prefixWord, tailWord_5972856, baseEnd_5972856] using wordTrace_append hprefix tailTrace_5972856
  have hstable : (prefixWord ++ tailWord_5972856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5972856).length < 2 ^ (prefixWord ++ tailWord_5972856).sum := by decide
  have hdescent : baseEnd_5972856 < baseStart_5972856 := by decide
  rcases family_descends (prefixWord ++ tailWord_5972856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5972876 : List Nat := [2, 2, 1, 2, 1, 2, 3, 1, 3, 1, 5]
def baseStart_5972876 : Nat := 118140960795 + 5972876 * 2 ^ 59
def prefixEnd_5972876 : Nat := 4983230072969 + 3 ^ 40 * 5972876 * 2
def baseEnd_5972876 : Nat := 3066956277704078328881249

theorem tailTrace_5972876 : CollatzResearch.WordTrace tailWord_5972876 prefixEnd_5972876 3066956277704078328881249 := by
  unfold tailWord_5972876
  simp only [CollatzResearch.WordTrace]
  refine ⟨108924342354648906426357241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145232456472865208568476321 108924342354648906426357241)
  ·
    refine ⟨81693256765986679819767931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108924342354648906426357241 81693256765986679819767931)
    ·
      refine ⟨122539885148980019729651897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81693256765986679819767931 122539885148980019729651897)
      ·
        refine ⟨91904913861735014797238923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122539885148980019729651897 91904913861735014797238923)
        ·
          refine ⟨137857370792602522195858385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91904913861735014797238923 137857370792602522195858385)
          ·
            refine ⟨103393028094451891646893789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137857370792602522195858385 103393028094451891646893789)
            ·
              refine ⟨38772385535419459367585171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103393028094451891646893789 38772385535419459367585171)
              ·
                refine ⟨58158578303129189051377757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38772385535419459367585171 58158578303129189051377757)
                ·
                  refine ⟨21809466863673445894266659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58158578303129189051377757 21809466863673445894266659)
                  ·
                    refine ⟨32714200295510168841399989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21809466863673445894266659 32714200295510168841399989)
                    ·
                      refine ⟨3066956277704078328881249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32714200295510168841399989 3066956277704078328881249)
                      ·
                        rfl

theorem cell23_5972876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_5972876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5972876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5972876 prefixEnd_5972876 := by exact prefixLift 5972876
  have htrace : WordTrace (prefixWord ++ tailWord_5972876) baseStart_5972876 baseEnd_5972876 := by
    simpa [prefixWord, tailWord_5972876, baseEnd_5972876] using wordTrace_append hprefix tailTrace_5972876
  have hstable : (prefixWord ++ tailWord_5972876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5972876).length < 2 ^ (prefixWord ++ tailWord_5972876).sum := by decide
  have hdescent : baseEnd_5972876 < baseStart_5972876 := by decide
  rcases family_descends (prefixWord ++ tailWord_5972876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5972913 : List Nat := [1, 2, 2, 4, 3, 2, 9]
def baseStart_5972913 : Nat := 118140960795 + 5972913 * 2 ^ 59
def prefixEnd_5972913 : Nat := 4983230072969 + 3 ^ 40 * 5972913 * 2
def baseEnd_5972913 : Nat := 37863892302324625729859

theorem tailTrace_5972913 : CollatzResearch.WordTrace tailWord_5972913 prefixEnd_5972913 37863892302324625729859 := by
  unfold tailWord_5972913
  simp only [CollatzResearch.WordTrace]
  refine ⟨217850034210163768171811393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145233356140109178781207595 217850034210163768171811393)
  ·
    refine ⟨163387525657622826128858545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217850034210163768171811393 163387525657622826128858545)
    ·
      refine ⟨122540644243217119596643909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163387525657622826128858545 122540644243217119596643909)
      ·
        refine ⟨22976370795603209924370733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122540644243217119596643909 22976370795603209924370733)
        ·
          refine ⟨8616139048351203721639025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22976370795603209924370733 8616139048351203721639025)
          ·
            refine ⟨6462104286263402791229269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8616139048351203721639025 6462104286263402791229269)
            ·
              refine ⟨37863892302324625729859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6462104286263402791229269 37863892302324625729859)
              ·
                rfl

theorem cell23_5972913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 9].length) (baseStart_5972913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5972913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5972913 prefixEnd_5972913 := by exact prefixLift 5972913
  have htrace : WordTrace (prefixWord ++ tailWord_5972913) baseStart_5972913 baseEnd_5972913 := by
    simpa [prefixWord, tailWord_5972913, baseEnd_5972913] using wordTrace_append hprefix tailTrace_5972913
  have hstable : (prefixWord ++ tailWord_5972913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5972913).length < 2 ^ (prefixWord ++ tailWord_5972913).sum := by decide
  have hdescent : baseEnd_5972913 < baseStart_5972913 := by decide
  rcases family_descends (prefixWord ++ tailWord_5972913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5972918 : List Nat := [5, 1, 4, 1, 1, 2, 1, 1, 3, 1, 3]
def baseStart_5972918 : Nat := 118140960795 + 5972918 * 2 ^ 59
def prefixEnd_5972918 : Nat := 4983230072969 + 3 ^ 40 * 5972918 * 2
def baseEnd_5972918 : Nat := 3066977843891567164556057

theorem tailTrace_5972918 : CollatzResearch.WordTrace tailWord_5972918 prefixEnd_5972918 3066977843891567164556057 := by
  unfold tailWord_5972918
  simp only [CollatzResearch.WordTrace]
  refine ⟨13615638535946603376608963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145233477716763769350495605 13615638535946603376608963)
  ·
    refine ⟨20423457803919905064913445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13615638535946603376608963 20423457803919905064913445)
    ·
      refine ⟨3829398338234982199671271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20423457803919905064913445 3829398338234982199671271)
      ·
        refine ⟨5744097507352473299506907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3829398338234982199671271 5744097507352473299506907)
        ·
          refine ⟨8616146261028709949260361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5744097507352473299506907 8616146261028709949260361)
          ·
            refine ⟨6462109695771532461945271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8616146261028709949260361 6462109695771532461945271)
            ·
              refine ⟨9693164543657298692917907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6462109695771532461945271 9693164543657298692917907)
              ·
                refine ⟨14539746815485948039376861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9693164543657298692917907 14539746815485948039376861)
                ·
                  refine ⟨5452405055807230514766323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14539746815485948039376861 5452405055807230514766323)
                  ·
                    refine ⟨8178607583710845772149485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5452405055807230514766323 8178607583710845772149485)
                    ·
                      refine ⟨3066977843891567164556057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8178607583710845772149485 3066977843891567164556057)
                      ·
                        rfl

theorem cell23_5972918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_5972918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5972918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5972918 prefixEnd_5972918 := by exact prefixLift 5972918
  have htrace : WordTrace (prefixWord ++ tailWord_5972918) baseStart_5972918 baseEnd_5972918 := by
    simpa [prefixWord, tailWord_5972918, baseEnd_5972918] using wordTrace_append hprefix tailTrace_5972918
  have hstable : (prefixWord ++ tailWord_5972918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5972918).length < 2 ^ (prefixWord ++ tailWord_5972918).sum := by decide
  have hdescent : baseEnd_5972918 < baseStart_5972918 := by decide
  rcases family_descends (prefixWord ++ tailWord_5972918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5972923 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 8, 1, 3]
def baseStart_5972923 : Nat := 118140960795 + 5972923 * 2 ^ 59
def prefixEnd_5972923 : Nat := 4983230072969 + 3 ^ 40 * 5972923 * 2
def baseEnd_5972923 : Nat := 3066980411294839644993533

theorem tailTrace_5972923 : CollatzResearch.WordTrace tailWord_5972923 prefixEnd_5972923 3066980411294839644993533 := by
  unfold tailWord_5972923
  simp only [CollatzResearch.WordTrace]
  refine ⟨217850398940127539879675423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145233599293418359919783615 217850398940127539879675423)
  ·
    refine ⟨326775598410191309819513135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217850398940127539879675423 326775598410191309819513135)
    ·
      refine ⟨490163397615286964729269703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326775598410191309819513135 490163397615286964729269703)
      ·
        refine ⟨735245096422930447093904555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 490163397615286964729269703 735245096422930447093904555)
        ·
          refine ⟨1102867644634395670640856833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 735245096422930447093904555 1102867644634395670640856833)
          ·
            refine ⟨827150733475796752980642625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1102867644634395670640856833 827150733475796752980642625)
            ·
              refine ⟨620363050106847564735481969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 827150733475796752980642625 620363050106847564735481969)
              ·
                refine ⟨465272287580135673551611477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 620363050106847564735481969 465272287580135673551611477)
                ·
                  refine ⟨5452409620079714924432947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 465272287580135673551611477 5452409620079714924432947)
                  ·
                    refine ⟨8178614430119572386649421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5452409620079714924432947 8178614430119572386649421)
                    ·
                      refine ⟨3066980411294839644993533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8178614430119572386649421 3066980411294839644993533)
                      ·
                        rfl

theorem cell23_5972923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 8, 1, 3].length) (baseStart_5972923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5972923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5972923 prefixEnd_5972923 := by exact prefixLift 5972923
  have htrace : WordTrace (prefixWord ++ tailWord_5972923) baseStart_5972923 baseEnd_5972923 := by
    simpa [prefixWord, tailWord_5972923, baseEnd_5972923] using wordTrace_append hprefix tailTrace_5972923
  have hstable : (prefixWord ++ tailWord_5972923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5972923).length < 2 ^ (prefixWord ++ tailWord_5972923).sum := by decide
  have hdescent : baseEnd_5972923 < baseStart_5972923 := by decide
  rcases family_descends (prefixWord ++ tailWord_5972923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5972974 : List Nat := [4, 1, 2, 1, 4, 1, 2, 2, 2, 1, 3]
def baseStart_5972974 : Nat := 118140960795 + 5972974 * 2 ^ 59
def prefixEnd_5972974 : Nat := 4983230072969 + 3 ^ 40 * 5972974 * 2
def baseEnd_5972974 : Nat := 3067006598808218945455799

theorem tailTrace_5972974 : CollatzResearch.WordTrace tailWord_5972974 prefixEnd_5972974 3067006598808218945455799 := by
  unfold tailWord_5972974
  simp only [CollatzResearch.WordTrace]
  refine ⟨27231532382867846948722747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145234839375295183726521317 27231532382867846948722747)
  ·
    refine ⟨40847298574301770423084121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27231532382867846948722747 40847298574301770423084121)
    ·
      refine ⟨30635473930726327817313091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40847298574301770423084121 30635473930726327817313091)
      ·
        refine ⟨45953210896089491725969637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30635473930726327817313091 45953210896089491725969637)
        ·
          refine ⟨8616227043016779698619307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45953210896089491725969637 8616227043016779698619307)
          ·
            refine ⟨12924340564525169547928961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8616227043016779698619307 12924340564525169547928961)
            ·
              refine ⟨9693255423393877160946721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12924340564525169547928961 9693255423393877160946721)
              ·
                refine ⟨7269941567545407870710041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9693255423393877160946721 7269941567545407870710041)
                ·
                  refine ⟨5452456175659055903032531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7269941567545407870710041 5452456175659055903032531)
                  ·
                    refine ⟨8178684263488583854548797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5452456175659055903032531 8178684263488583854548797)
                    ·
                      refine ⟨3067006598808218945455799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8178684263488583854548797 3067006598808218945455799)
                      ·
                        rfl

theorem cell23_5972974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 2, 2, 1, 3].length) (baseStart_5972974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5972974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5972974 prefixEnd_5972974 := by exact prefixLift 5972974
  have htrace : WordTrace (prefixWord ++ tailWord_5972974) baseStart_5972974 baseEnd_5972974 := by
    simpa [prefixWord, tailWord_5972974, baseEnd_5972974] using wordTrace_append hprefix tailTrace_5972974
  have hstable : (prefixWord ++ tailWord_5972974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5972974).length < 2 ^ (prefixWord ++ tailWord_5972974).sum := by decide
  have hdescent : baseEnd_5972974 < baseStart_5972974 := by decide
  rcases family_descends (prefixWord ++ tailWord_5972974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5972976 : List Nat := [2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 6]
def baseStart_5972976 : Nat := 118140960795 + 5972976 * 2 ^ 59
def prefixEnd_5972976 : Nat := 4983230072969 + 3 ^ 40 * 5972976 * 2
def baseEnd_5972976 : Nat := 3067007625769527937630789

theorem tailTrace_5972976 : CollatzResearch.WordTrace tailWord_5972976 prefixEnd_5972976 3067007625769527937630789 := by
  unfold tailWord_5972976
  simp only [CollatzResearch.WordTrace]
  refine ⟨108926166004467764965677391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145234888005957019954236521 108926166004467764965677391)
  ·
    refine ⟨163389249006701647448516087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108926166004467764965677391 163389249006701647448516087)
    ·
      refine ⟨245083873510052471172774131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163389249006701647448516087 245083873510052471172774131)
      ·
        refine ⟨367625810265078706759161197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245083873510052471172774131 367625810265078706759161197)
        ·
          refine ⟨137859678849404515034685449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 367625810265078706759161197 137859678849404515034685449)
          ·
            refine ⟨103394759137053386276014087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137859678849404515034685449 103394759137053386276014087)
            ·
              refine ⟨155092138705580079414021131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103394759137053386276014087 155092138705580079414021131)
              ·
                refine ⟨232638208058370119121031697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155092138705580079414021131 232638208058370119121031697)
                ·
                  refine ⟨174478656043777589340773773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 232638208058370119121031697 174478656043777589340773773)
                  ·
                    refine ⟨65429496016416596002790165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 174478656043777589340773773 65429496016416596002790165)
                    ·
                      refine ⟨3067007625769527937630789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65429496016416596002790165 3067007625769527937630789)
                      ·
                        rfl

theorem cell23_5972976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 6].length) (baseStart_5972976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5972976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5972976 prefixEnd_5972976 := by exact prefixLift 5972976
  have htrace : WordTrace (prefixWord ++ tailWord_5972976) baseStart_5972976 baseEnd_5972976 := by
    simpa [prefixWord, tailWord_5972976, baseEnd_5972976] using wordTrace_append hprefix tailTrace_5972976
  have hstable : (prefixWord ++ tailWord_5972976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5972976).length < 2 ^ (prefixWord ++ tailWord_5972976).sum := by decide
  have hdescent : baseEnd_5972976 < baseStart_5972976 := by decide
  rcases family_descends (prefixWord ++ tailWord_5972976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5972986 : List Nat := [3, 1, 1, 1, 1, 2, 1, 2, 11]
def baseStart_5972986 : Nat := 118140960795 + 5972986 * 2 ^ 59
def prefixEnd_5972986 : Nat := 4983230072969 + 3 ^ 40 * 5972986 * 2
def baseEnd_5972986 : Nat := 340779195619563655389527

theorem tailTrace_5972986 : CollatzResearch.WordTrace tailWord_5972986 prefixEnd_5972986 340779195619563655389527 := by
  unfold tailWord_5972986
  simp only [CollatzResearch.WordTrace]
  refine ⟨54463174184724825409804703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145235131159266201092812541 54463174184724825409804703)
  ·
    refine ⟨81694761277087238114707055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54463174184724825409804703 81694761277087238114707055)
    ·
      refine ⟨122542141915630857172060583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81694761277087238114707055 122542141915630857172060583)
      ·
        refine ⟨183813212873446285758090875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122542141915630857172060583 183813212873446285758090875)
        ·
          refine ⟨275719819310169428637136313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183813212873446285758090875 275719819310169428637136313)
          ·
            refine ⟨206789864482627071477852235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 275719819310169428637136313 206789864482627071477852235)
            ·
              refine ⟨310184796723940607216778353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206789864482627071477852235 310184796723940607216778353)
              ·
                refine ⟨232638597542955455412583765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 310184796723940607216778353 232638597542955455412583765)
                ·
                  refine ⟨340779195619563655389527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 232638597542955455412583765 340779195619563655389527)
                  ·
                    rfl

theorem cell23_5972986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 11].length) (baseStart_5972986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5972986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5972986 prefixEnd_5972986 := by exact prefixLift 5972986
  have htrace : WordTrace (prefixWord ++ tailWord_5972986) baseStart_5972986 baseEnd_5972986 := by
    simpa [prefixWord, tailWord_5972986, baseEnd_5972986] using wordTrace_append hprefix tailTrace_5972986
  have hstable : (prefixWord ++ tailWord_5972986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5972986).length < 2 ^ (prefixWord ++ tailWord_5972986).sum := by decide
  have hdescent : baseEnd_5972986 < baseStart_5972986 := by decide
  rcases family_descends (prefixWord ++ tailWord_5972986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5972993 : List Nat := [1, 2, 4, 1, 2, 2, 1, 1, 1, 4, 4]
def baseStart_5972993 : Nat := 118140960795 + 5972993 * 2 ^ 59
def prefixEnd_5972993 : Nat := 4983230072969 + 3 ^ 40 * 5972993 * 2
def baseEnd_5972993 : Nat := 3067016354940654371118211

theorem tailTrace_5972993 : CollatzResearch.WordTrace tailWord_5972993 prefixEnd_5972993 3067016354940654371118211 := by
  unfold tailWord_5972993
  simp only [CollatzResearch.WordTrace]
  refine ⟨217852952049873941834723633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145235301366582627889815755 217852952049873941834723633)
  ·
    refine ⟨163389714037405456376042725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217852952049873941834723633 163389714037405456376042725)
    ·
      refine ⟨30635571382013523070508011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163389714037405456376042725 30635571382013523070508011)
      ·
        refine ⟨45953357073020284605762017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30635571382013523070508011 45953357073020284605762017)
        ·
          refine ⟨34465017804765213454321513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45953357073020284605762017 34465017804765213454321513)
          ·
            refine ⟨25848763353573910090741135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34465017804765213454321513 25848763353573910090741135)
            ·
              refine ⟨38773145030360865136111703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25848763353573910090741135 38773145030360865136111703)
              ·
                refine ⟨58159717545541297704167555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38773145030360865136111703 58159717545541297704167555)
                ·
                  refine ⟨87239576318311946556251333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58159717545541297704167555 87239576318311946556251333)
                  ·
                    refine ⟨16357420559683489979297125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 87239576318311946556251333 16357420559683489979297125)
                    ·
                      refine ⟨3067016354940654371118211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16357420559683489979297125 3067016354940654371118211)
                      ·
                        rfl

theorem cell23_5972993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_5972993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5972993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5972993 prefixEnd_5972993 := by exact prefixLift 5972993
  have htrace : WordTrace (prefixWord ++ tailWord_5972993) baseStart_5972993 baseEnd_5972993 := by
    simpa [prefixWord, tailWord_5972993, baseEnd_5972993] using wordTrace_append hprefix tailTrace_5972993
  have hstable : (prefixWord ++ tailWord_5972993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5972993).length < 2 ^ (prefixWord ++ tailWord_5972993).sum := by decide
  have hdescent : baseEnd_5972993 < baseStart_5972993 := by decide
  rcases family_descends (prefixWord ++ tailWord_5972993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5972997 : List Nat := [1, 3, 1, 1, 2, 3, 1, 5, 2, 2, 2]
def baseStart_5972997 : Nat := 118140960795 + 5972997 * 2 ^ 59
def prefixEnd_5972997 : Nat := 4983230072969 + 3 ^ 40 * 5972997 * 2
def baseEnd_5972997 : Nat := 3067018408863272355468193

theorem tailTrace_5972997 : CollatzResearch.WordTrace tailWord_5972997 prefixEnd_5972997 3067018408863272355468193 := by
  unfold tailWord_5972997
  simp only [CollatzResearch.WordTrace]
  refine ⟨217853097941859450517869245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145235398627906300345246163 217853097941859450517869245)
  ·
    refine ⟨81694911728197293944200967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217853097941859450517869245 81694911728197293944200967)
    ·
      refine ⟨122542367592295940916301451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81694911728197293944200967 122542367592295940916301451)
      ·
        refine ⟨183813551388443911374452177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122542367592295940916301451 183813551388443911374452177)
        ·
          refine ⟨137860163541332933530839133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183813551388443911374452177 137860163541332933530839133)
          ·
            refine ⟨51697561327999850074064675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137860163541332933530839133 51697561327999850074064675)
            ·
              refine ⟨77546341991999775111097013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51697561327999850074064675 77546341991999775111097013)
              ·
                refine ⟨7269969561749978916665345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77546341991999775111097013 7269969561749978916665345)
                ·
                  refine ⟨5452477171312484187499009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7269969561749978916665345 5452477171312484187499009)
                  ·
                    refine ⟨4089357878484363140624257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5452477171312484187499009 4089357878484363140624257)
                    ·
                      refine ⟨3067018408863272355468193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4089357878484363140624257 3067018408863272355468193)
                      ·
                        rfl

theorem cell23_5972997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 5, 2, 2, 2].length) (baseStart_5972997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5972997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5972997 prefixEnd_5972997 := by exact prefixLift 5972997
  have htrace : WordTrace (prefixWord ++ tailWord_5972997) baseStart_5972997 baseEnd_5972997 := by
    simpa [prefixWord, tailWord_5972997, baseEnd_5972997] using wordTrace_append hprefix tailTrace_5972997
  have hstable : (prefixWord ++ tailWord_5972997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5972997).length < 2 ^ (prefixWord ++ tailWord_5972997).sum := by decide
  have hdescent : baseEnd_5972997 < baseStart_5972997 := by decide
  rcases family_descends (prefixWord ++ tailWord_5972997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5973003 : List Nat := [1, 1, 1, 1, 6, 3, 1, 2, 7]
def baseStart_5973003 : Nat := 118140960795 + 5973003 * 2 ^ 59
def prefixEnd_5973003 : Nat := 4983230072969 + 3 ^ 40 * 5973003 * 2
def baseEnd_5973003 : Nat := 340780165527466592443685

theorem tailTrace_5973003 : CollatzResearch.WordTrace tailWord_5973003 prefixEnd_5973003 340780165527466592443685 := by
  unfold tailWord_5973003
  simp only [CollatzResearch.WordTrace]
  refine ⟨217853316779837713542587663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145235544519891809028391775 217853316779837713542587663)
  ·
    refine ⟨326779975169756570313881495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217853316779837713542587663 326779975169756570313881495)
    ·
      refine ⟨490169962754634855470822243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326779975169756570313881495 490169962754634855470822243)
      ·
        refine ⟨735254944131952283206233365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 490169962754634855470822243 735254944131952283206233365)
        ·
          refine ⟨34465075506185263275292189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 735254944131952283206233365 34465075506185263275292189)
          ·
            refine ⟨12924403314819473728234571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34465075506185263275292189 12924403314819473728234571)
            ·
              refine ⟨19386604972229210592351857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12924403314819473728234571 19386604972229210592351857)
              ·
                refine ⟨14539953729171907944263893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19386604972229210592351857 14539953729171907944263893)
                ·
                  refine ⟨340780165527466592443685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14539953729171907944263893 340780165527466592443685)
                  ·
                    rfl

theorem cell23_5973003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 2, 7].length) (baseStart_5973003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5973003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5973003 prefixEnd_5973003 := by exact prefixLift 5973003
  have htrace : WordTrace (prefixWord ++ tailWord_5973003) baseStart_5973003 baseEnd_5973003 := by
    simpa [prefixWord, tailWord_5973003, baseEnd_5973003] using wordTrace_append hprefix tailTrace_5973003
  have hstable : (prefixWord ++ tailWord_5973003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5973003).length < 2 ^ (prefixWord ++ tailWord_5973003).sum := by decide
  have hdescent : baseEnd_5973003 < baseStart_5973003 := by decide
  rcases family_descends (prefixWord ++ tailWord_5973003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5973031 : List Nat := [1, 1, 7, 1, 1, 1, 3, 2, 2, 2, 2]
def baseStart_5973031 : Nat := 118140960795 + 5973031 * 2 ^ 59
def prefixEnd_5973031 : Nat := 4983230072969 + 3 ^ 40 * 5973031 * 2
def baseEnd_5973031 : Nat := 3067035867205525222443037

theorem tailTrace_5973031 : CollatzResearch.WordTrace tailWord_5973031 prefixEnd_5973031 3067035867205525222443037 := by
  unfold tailWord_5973031
  simp only [CollatzResearch.WordTrace]
  refine ⟨217854338023736274324606947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145236225349157516216404631 217854338023736274324606947)
  ·
    refine ⟨326781507035604411486910421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217854338023736274324606947 326781507035604411486910421)
    ·
      refine ⟨7658941571146978394224463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 326781507035604411486910421 7658941571146978394224463)
      ·
        refine ⟨11488412356720467591336695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7658941571146978394224463 11488412356720467591336695)
        ·
          refine ⟨17232618535080701387005043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11488412356720467591336695 17232618535080701387005043)
          ·
            refine ⟨25848927802621052080507565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17232618535080701387005043 25848927802621052080507565)
            ·
              refine ⟨9693347925982894530190337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25848927802621052080507565 9693347925982894530190337)
              ·
                refine ⟨7270010944487170897642753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9693347925982894530190337 7270010944487170897642753)
                ·
                  refine ⟨5452508208365378173232065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7270010944487170897642753 5452508208365378173232065)
                  ·
                    refine ⟨4089381156274033629924049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5452508208365378173232065 4089381156274033629924049)
                    ·
                      refine ⟨3067035867205525222443037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4089381156274033629924049 3067035867205525222443037)
                      ·
                        rfl

theorem cell23_5973031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_5973031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5973031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5973031 prefixEnd_5973031 := by exact prefixLift 5973031
  have htrace : WordTrace (prefixWord ++ tailWord_5973031) baseStart_5973031 baseEnd_5973031 := by
    simpa [prefixWord, tailWord_5973031, baseEnd_5973031] using wordTrace_append hprefix tailTrace_5973031
  have hstable : (prefixWord ++ tailWord_5973031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5973031).length < 2 ^ (prefixWord ++ tailWord_5973031).sum := by decide
  have hdescent : baseEnd_5973031 < baseStart_5973031 := by decide
  rcases family_descends (prefixWord ++ tailWord_5973031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5973070 : List Nat := [4, 1, 1, 1, 1, 3, 2, 3, 2, 1, 4]
def baseStart_5973070 : Nat := 118140960795 + 5973070 * 2 ^ 59
def prefixEnd_5973070 : Nat := 4983230072969 + 3 ^ 40 * 5973070 * 2
def baseEnd_5973070 : Nat := 3067055892951050569855357

theorem tailTrace_5973070 : CollatzResearch.WordTrace tailWord_5973070 prefixEnd_5973070 3067055892951050569855357 := by
  unfold tailWord_5973070
  simp only [CollatzResearch.WordTrace]
  refine ⟨27231970058824372998159583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145237173647063322656851109 27231970058824372998159583)
  ·
    refine ⟨40847955088236559497239375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27231970058824372998159583 40847955088236559497239375)
    ·
      refine ⟨61271932632354839245859063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40847955088236559497239375 61271932632354839245859063)
      ·
        refine ⟨91907898948532258868788595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61271932632354839245859063 91907898948532258868788595)
        ·
          refine ⟨137861848422798388303182893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91907898948532258868788595 137861848422798388303182893)
          ·
            refine ⟨51698193158549395613693585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137861848422798388303182893 51698193158549395613693585)
            ·
              refine ⟨38773644868912046710270189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51698193158549395613693585 38773644868912046710270189)
              ·
                refine ⟨14540116825842017516351321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38773644868912046710270189 14540116825842017516351321)
                ·
                  refine ⟨10905087619381513137263491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14540116825842017516351321 10905087619381513137263491)
                  ·
                    refine ⟨16357631429072269705895237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10905087619381513137263491 16357631429072269705895237)
                    ·
                      refine ⟨3067055892951050569855357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16357631429072269705895237 3067055892951050569855357)
                      ·
                        rfl

theorem cell23_5973070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 3, 2, 1, 4].length) (baseStart_5973070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5973070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5973070 prefixEnd_5973070 := by exact prefixLift 5973070
  have htrace : WordTrace (prefixWord ++ tailWord_5973070) baseStart_5973070 baseEnd_5973070 := by
    simpa [prefixWord, tailWord_5973070, baseEnd_5973070] using wordTrace_append hprefix tailTrace_5973070
  have hstable : (prefixWord ++ tailWord_5973070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5973070).length < 2 ^ (prefixWord ++ tailWord_5973070).sum := by decide
  have hdescent : baseEnd_5973070 < baseStart_5973070 := by decide
  rcases family_descends (prefixWord ++ tailWord_5973070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5973093 : List Nat := [1, 3, 1, 3, 2, 1, 1, 3, 8]
def baseStart_5973093 : Nat := 118140960795 + 5973093 * 2 ^ 59
def prefixEnd_5973093 : Nat := 4983230072969 + 3 ^ 40 * 5973093 * 2
def baseEnd_5973093 : Nat := 340785300334011553318639

theorem tailTrace_5973093 : CollatzResearch.WordTrace tailWord_5973093 prefixEnd_5973093 340785300334011553318639 := by
  unfold tailWord_5973093
  simp only [CollatzResearch.WordTrace]
  refine ⟨217856599349511658913363933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145237732899674439275575955 217856599349511658913363933)
  ·
    refine ⟨81696224756066872092511475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217856599349511658913363933 81696224756066872092511475)
    ·
      refine ⟨122544337134100308138767213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81696224756066872092511475 122544337134100308138767213)
      ·
        refine ⟨45954126425287615552037705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122544337134100308138767213 45954126425287615552037705)
        ·
          refine ⟨34465594818965711664028279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45954126425287615552037705 34465594818965711664028279)
          ·
            refine ⟨51698392228448567496042419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34465594818965711664028279 51698392228448567496042419)
            ·
              refine ⟨77547588342672851244063629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51698392228448567496042419 77547588342672851244063629)
              ·
                refine ⟨29080345628502319216523861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77547588342672851244063629 29080345628502319216523861)
                ·
                  refine ⟨340785300334011553318639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29080345628502319216523861 340785300334011553318639)
                  ·
                    rfl

theorem cell23_5973093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 8].length) (baseStart_5973093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5973093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5973093 prefixEnd_5973093 := by exact prefixLift 5973093
  have htrace : WordTrace (prefixWord ++ tailWord_5973093) baseStart_5973093 baseEnd_5973093 := by
    simpa [prefixWord, tailWord_5973093, baseEnd_5973093] using wordTrace_append hprefix tailTrace_5973093
  have hstable : (prefixWord ++ tailWord_5973093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5973093).length < 2 ^ (prefixWord ++ tailWord_5973093).sum := by decide
  have hdescent : baseEnd_5973093 < baseStart_5973093 := by decide
  rcases family_descends (prefixWord ++ tailWord_5973093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5973097 : List Nat := [1, 2, 1, 1, 1, 8, 1, 1, 3, 4]
def baseStart_5973097 : Nat := 118140960795 + 5973097 * 2 ^ 59
def prefixEnd_5973097 : Nat := 4983230072969 + 3 ^ 40 * 5973097 * 2
def baseEnd_5973097 : Nat := 1022356585642907321405911

theorem tailTrace_5973097 : CollatzResearch.WordTrace tailWord_5973097 prefixEnd_5973097 1022356585642907321405911 := by
  unfold tailWord_5973097
  simp only [CollatzResearch.WordTrace]
  refine ⟨217856745241497167596509545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145237830160998111731006363 217856745241497167596509545)
  ·
    refine ⟨163392558931122875697382159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217856745241497167596509545 163392558931122875697382159)
    ·
      refine ⟨245088838396684313546073239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163392558931122875697382159 245088838396684313546073239)
      ·
        refine ⟨367633257595026470319109859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245088838396684313546073239 367633257595026470319109859)
        ·
          refine ⟨551449886392539705478664789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367633257595026470319109859 551449886392539705478664789)
          ·
            refine ⟨6462303356162574673578103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 551449886392539705478664789 6462303356162574673578103)
            ·
              refine ⟨9693455034243862010367155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6462303356162574673578103 9693455034243862010367155)
              ·
                refine ⟨14540182551365793015550733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9693455034243862010367155 14540182551365793015550733)
                ·
                  refine ⟨5452568456762172380831525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14540182551365793015550733 5452568456762172380831525)
                  ·
                    refine ⟨1022356585642907321405911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5452568456762172380831525 1022356585642907321405911)
                    ·
                      rfl

theorem cell23_5973097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 1, 3, 4].length) (baseStart_5973097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5973097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5973097 prefixEnd_5973097 := by exact prefixLift 5973097
  have htrace : WordTrace (prefixWord ++ tailWord_5973097) baseStart_5973097 baseEnd_5973097 := by
    simpa [prefixWord, tailWord_5973097, baseEnd_5973097] using wordTrace_append hprefix tailTrace_5973097
  have hstable : (prefixWord ++ tailWord_5973097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5973097).length < 2 ^ (prefixWord ++ tailWord_5973097).sum := by decide
  have hdescent : baseEnd_5973097 < baseStart_5973097 := by decide
  rcases family_descends (prefixWord ++ tailWord_5973097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5973170 : List Nat := [3, 2, 1, 1, 1, 4, 1, 3, 1, 6]
def baseStart_5973170 : Nat := 118140960795 + 5973170 * 2 ^ 59
def prefixEnd_5973170 : Nat := 4983230072969 + 3 ^ 40 * 5973170 * 2
def baseEnd_5973170 : Nat := 1022369080338833392868299

theorem tailTrace_5973170 : CollatzResearch.WordTrace tailWord_5973170 prefixEnd_5973170 1022369080338833392868299 := by
  unfold tailWord_5973170
  simp only [CollatzResearch.WordTrace]
  refine ⟨54464851942558175265979241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145239605180155134042611309 54464851942558175265979241)
  ·
    refine ⟨40848638956918631449484431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54464851942558175265979241 40848638956918631449484431)
    ·
      refine ⟨61272958435377947174226647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40848638956918631449484431 61272958435377947174226647)
      ·
        refine ⟨91909437653066920761339971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61272958435377947174226647 91909437653066920761339971)
        ·
          refine ⟨137864156479600381142009957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91909437653066920761339971 137864156479600381142009957)
          ·
            refine ⟨25849529339925071464126867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 137864156479600381142009957 25849529339925071464126867)
            ·
              refine ⟨38774294009887607196190301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25849529339925071464126867 38774294009887607196190301)
              ·
                refine ⟨14540360253707852698571363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38774294009887607196190301 14540360253707852698571363)
                ·
                  refine ⟨21810540380561779047857045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14540360253707852698571363 21810540380561779047857045)
                  ·
                    refine ⟨1022369080338833392868299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21810540380561779047857045 1022369080338833392868299)
                    ·
                      rfl

theorem cell23_5973170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 3, 1, 6].length) (baseStart_5973170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5973170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5973170 prefixEnd_5973170 := by exact prefixLift 5973170
  have htrace : WordTrace (prefixWord ++ tailWord_5973170) baseStart_5973170 baseEnd_5973170 := by
    simpa [prefixWord, tailWord_5973170, baseEnd_5973170] using wordTrace_append hprefix tailTrace_5973170
  have hstable : (prefixWord ++ tailWord_5973170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5973170).length < 2 ^ (prefixWord ++ tailWord_5973170).sum := by decide
  have hdescent : baseEnd_5973170 < baseStart_5973170 := by decide
  rcases family_descends (prefixWord ++ tailWord_5973170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5973183 : List Nat := [1, 1, 2, 2, 2, 2, 2, 11]
def baseStart_5973183 : Nat := 118140960795 + 5973183 * 2 ^ 59
def prefixEnd_5973183 : Nat := 4983230072969 + 3 ^ 40 * 5973183 * 2
def baseEnd_5973183 : Nat := 113596811713518838064531

theorem tailTrace_5973183 : CollatzResearch.WordTrace tailWord_5973183 prefixEnd_5973183 113596811713518838064531 := by
  unfold tailWord_5973183
  simp only [CollatzResearch.WordTrace]
  refine ⟨217859881919185604284140203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145239921279457069522760135 217859881919185604284140203)
  ·
    refine ⟨326789822878778406426210305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217859881919185604284140203 326789822878778406426210305)
    ·
      refine ⟨245092367159083804819657729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326789822878778406426210305 245092367159083804819657729)
      ·
        refine ⟨183819275369312853614743297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245092367159083804819657729 183819275369312853614743297)
        ·
          refine ⟨137864456526984640211057473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183819275369312853614743297 137864456526984640211057473)
          ·
            refine ⟨103398342395238480158293105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137864456526984640211057473 103398342395238480158293105)
            ·
              refine ⟨77548756796428860118719829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103398342395238480158293105 77548756796428860118719829)
              ·
                refine ⟨113596811713518838064531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 77548756796428860118719829 113596811713518838064531)
                ·
                  rfl

theorem cell23_5973183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 11].length) (baseStart_5973183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5973183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5973183 prefixEnd_5973183 := by exact prefixLift 5973183
  have htrace : WordTrace (prefixWord ++ tailWord_5973183) baseStart_5973183 baseEnd_5973183 := by
    simpa [prefixWord, tailWord_5973183, baseEnd_5973183] using wordTrace_append hprefix tailTrace_5973183
  have hstable : (prefixWord ++ tailWord_5973183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5973183).length < 2 ^ (prefixWord ++ tailWord_5973183).sum := by decide
  have hdescent : baseEnd_5973183 < baseStart_5973183 := by decide
  rcases family_descends (prefixWord ++ tailWord_5973183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5973188 : List Nat := [2, 3, 3, 1, 3, 1, 2, 3, 1, 1, 3]
def baseStart_5973188 : Nat := 118140960795 + 5973188 * 2 ^ 59
def prefixEnd_5973188 : Nat := 4983230072969 + 3 ^ 40 * 5973188 * 2
def baseEnd_5973188 : Nat := 3067116483668281108179815

theorem tailTrace_5973188 : CollatzResearch.WordTrace tailWord_5973188 prefixEnd_5973188 3067116483668281108179815 := by
  unfold tailWord_5973188
  simp only [CollatzResearch.WordTrace]
  refine ⟨108930032142083745069036109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145240042856111660092048145 108930032142083745069036109)
  ·
    refine ⟨40848762053281404400888541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108930032142083745069036109 40848762053281404400888541)
    ·
      refine ⟨15318285769980526650333203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40848762053281404400888541 15318285769980526650333203)
      ·
        refine ⟨22977428654970789975499805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15318285769980526650333203 22977428654970789975499805)
        ·
          refine ⟨8616535745614046240812427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22977428654970789975499805 8616535745614046240812427)
          ·
            refine ⟨12924803618421069361218641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8616535745614046240812427 12924803618421069361218641)
            ·
              refine ⟨9693602713815802020913981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12924803618421069361218641 9693602713815802020913981)
              ·
                refine ⟨3635101017680925757842743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9693602713815802020913981 3635101017680925757842743)
                ·
                  refine ⟨5452651526521388636764115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3635101017680925757842743 5452651526521388636764115)
                  ·
                    refine ⟨8178977289782082955146173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5452651526521388636764115 8178977289782082955146173)
                    ·
                      refine ⟨3067116483668281108179815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8178977289782082955146173 3067116483668281108179815)
                      ·
                        rfl

theorem cell23_5973188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_5973188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5973188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5973188 prefixEnd_5973188 := by exact prefixLift 5973188
  have htrace : WordTrace (prefixWord ++ tailWord_5973188) baseStart_5973188 baseEnd_5973188 := by
    simpa [prefixWord, tailWord_5973188, baseEnd_5973188] using wordTrace_append hprefix tailTrace_5973188
  have hstable : (prefixWord ++ tailWord_5973188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5973188).length < 2 ^ (prefixWord ++ tailWord_5973188).sum := by decide
  have hdescent : baseEnd_5973188 < baseStart_5973188 := by decide
  rcases family_descends (prefixWord ++ tailWord_5973188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5973193 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 1, 4, 7]
def baseStart_5973193 : Nat := 118140960795 + 5973193 * 2 ^ 59
def prefixEnd_5973193 : Nat := 4983230072969 + 3 ^ 40 * 5973193 * 2
def baseEnd_5973193 : Nat := 3067119051071553588617291

theorem tailTrace_5973193 : CollatzResearch.WordTrace tailWord_5973193 prefixEnd_5973193 3067119051071553588617291 := by
  unfold tailWord_5973193
  simp only [CollatzResearch.WordTrace]
  refine ⟨217860246649149375992004233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145240164432766250661336155 217860246649149375992004233)
  ·
    refine ⟨163395184986862031994003175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217860246649149375992004233 163395184986862031994003175)
    ·
      refine ⟨245092777480293047991004763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163395184986862031994003175 245092777480293047991004763)
      ·
        refine ⟨367639166220439571986507145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245092777480293047991004763 367639166220439571986507145)
        ·
          refine ⟨275729374665329678989880359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 367639166220439571986507145 275729374665329678989880359)
          ·
            refine ⟨413594061997994518484820539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275729374665329678989880359 413594061997994518484820539)
            ·
              refine ⟨620391092996991777727230809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 413594061997994518484820539 620391092996991777727230809)
              ·
                refine ⟨465293319747743833295423107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 620391092996991777727230809 465293319747743833295423107)
                ·
                  refine ⟨697939979621615749943134661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 465293319747743833295423107 697939979621615749943134661)
                  ·
                    refine ⟨130863746179052953114337749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 697939979621615749943134661 130863746179052953114337749)
                    ·
                      refine ⟨3067119051071553588617291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 130863746179052953114337749 3067119051071553588617291)
                      ·
                        rfl

theorem cell23_5973193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 4, 7].length) (baseStart_5973193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5973193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5973193 prefixEnd_5973193 := by exact prefixLift 5973193
  have htrace : WordTrace (prefixWord ++ tailWord_5973193) baseStart_5973193 baseEnd_5973193 := by
    simpa [prefixWord, tailWord_5973193, baseEnd_5973193] using wordTrace_append hprefix tailTrace_5973193
  have hstable : (prefixWord ++ tailWord_5973193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5973193).length < 2 ^ (prefixWord ++ tailWord_5973193).sum := by decide
  have hdescent : baseEnd_5973193 < baseStart_5973193 := by decide
  rcases family_descends (prefixWord ++ tailWord_5973193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5973194 : List Nat := [3, 1, 2, 1, 3, 2, 4, 1, 1, 1, 4]
def baseStart_5973194 : Nat := 118140960795 + 5973194 * 2 ^ 59
def prefixEnd_5973194 : Nat := 4983230072969 + 3 ^ 40 * 5973194 * 2
def baseEnd_5973194 : Nat := 3067119564552208084704787

theorem tailTrace_5973194 : CollatzResearch.WordTrace tailWord_5973194 prefixEnd_5973194 3067119564552208084704787 := by
  unfold tailWord_5973194
  simp only [CollatzResearch.WordTrace]
  refine ⟨54465070780536438290697659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145240188748097168775193757 54465070780536438290697659)
  ·
    refine ⟨81697606170804657436046489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54465070780536438290697659 81697606170804657436046489)
    ·
      refine ⟨61273204628103493077034867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81697606170804657436046489 61273204628103493077034867)
      ·
        refine ⟨91909806942155239615552301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61273204628103493077034867 91909806942155239615552301)
        ·
          refine ⟨34466177603308214855832113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91909806942155239615552301 34466177603308214855832113)
          ·
            refine ⟨25849633202481161141874085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34466177603308214855832113 25849633202481161141874085)
            ·
              refine ⟨4846806225465217714101391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25849633202481161141874085 4846806225465217714101391)
              ·
                refine ⟨7270209338197826571152087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4846806225465217714101391 7270209338197826571152087)
                ·
                  refine ⟨10905314007296739856728131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7270209338197826571152087 10905314007296739856728131)
                  ·
                    refine ⟨16357971010945109785092197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10905314007296739856728131 16357971010945109785092197)
                    ·
                      refine ⟨3067119564552208084704787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16357971010945109785092197 3067119564552208084704787)
                      ·
                        rfl

theorem cell23_5973194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4, 1, 1, 1, 4].length) (baseStart_5973194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5973194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5973194 prefixEnd_5973194 := by exact prefixLift 5973194
  have htrace : WordTrace (prefixWord ++ tailWord_5973194) baseStart_5973194 baseEnd_5973194 := by
    simpa [prefixWord, tailWord_5973194, baseEnd_5973194] using wordTrace_append hprefix tailTrace_5973194
  have hstable : (prefixWord ++ tailWord_5973194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5973194).length < 2 ^ (prefixWord ++ tailWord_5973194).sum := by decide
  have hdescent : baseEnd_5973194 < baseStart_5973194 := by decide
  rcases family_descends (prefixWord ++ tailWord_5973194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5973221 : List Nat := [1, 3, 1, 4, 3, 1, 3, 1, 2, 4]
def baseStart_5973221 : Nat := 118140960795 + 5973221 * 2 ^ 59
def prefixEnd_5973221 : Nat := 4983230072969 + 3 ^ 40 * 5973221 * 2
def baseEnd_5973221 : Nat := 1022377809509959826355721

theorem tailTrace_5973221 : CollatzResearch.WordTrace tailWord_5973221 prefixEnd_5973221 1022377809509959826355721 := by
  unfold tailWord_5973221
  simp only [CollatzResearch.WordTrace]
  refine ⟨217861267893047936774023517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145240845262031957849349011 217861267893047936774023517)
  ·
    refine ⟨81697975459892976290258819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217861267893047936774023517 81697975459892976290258819)
    ·
      refine ⟨122546963189839464435388229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81697975459892976290258819 122546963189839464435388229)
      ·
        refine ⟨22977555598094899581635293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122546963189839464435388229 22977555598094899581635293)
        ·
          refine ⟨8616583349285587343113235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22977555598094899581635293 8616583349285587343113235)
          ·
            refine ⟨12924875023928381014669853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8616583349285587343113235 12924875023928381014669853)
            ·
              refine ⟨4846828133973142880501195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12924875023928381014669853 4846828133973142880501195)
              ·
                refine ⟨7270242200959714320751793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4846828133973142880501195 7270242200959714320751793)
                ·
                  refine ⟨5452681650719785740563845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7270242200959714320751793 5452681650719785740563845)
                  ·
                    refine ⟨1022377809509959826355721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5452681650719785740563845 1022377809509959826355721)
                    ·
                      rfl

theorem cell23_5973221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3, 1, 2, 4].length) (baseStart_5973221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5973221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5973221 prefixEnd_5973221 := by exact prefixLift 5973221
  have htrace : WordTrace (prefixWord ++ tailWord_5973221) baseStart_5973221 baseEnd_5973221 := by
    simpa [prefixWord, tailWord_5973221, baseEnd_5973221] using wordTrace_append hprefix tailTrace_5973221
  have hstable : (prefixWord ++ tailWord_5973221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5973221).length < 2 ^ (prefixWord ++ tailWord_5973221).sum := by decide
  have hdescent : baseEnd_5973221 < baseStart_5973221 := by decide
  rcases family_descends (prefixWord ++ tailWord_5973221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5973227 : List Nat := [1, 1, 1, 1, 2, 6, 3, 1, 1, 3, 3]
def baseStart_5973227 : Nat := 118140960795 + 5973227 * 2 ^ 59
def prefixEnd_5973227 : Nat := 4983230072969 + 3 ^ 40 * 5973227 * 2
def baseEnd_5973227 : Nat := 3067136509413806455592135

theorem tailTrace_5973227 : CollatzResearch.WordTrace tailWord_5973227 prefixEnd_5973227 3067136509413806455592135 := by
  unfold tailWord_5973227
  simp only [CollatzResearch.WordTrace]
  refine ⟨217861486731026199798741935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145240991154017466532494623 217861486731026199798741935)
  ·
    refine ⟨326792230096539299698112903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217861486731026199798741935 326792230096539299698112903)
    ·
      refine ⟨490188345144808949547169355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326792230096539299698112903 490188345144808949547169355)
      ·
        refine ⟨735282517717213424320754033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 490188345144808949547169355 735282517717213424320754033)
        ·
          refine ⟨551461888287910068240565525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 735282517717213424320754033 551461888287910068240565525)
          ·
            refine ⟨25849776013495784448776509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 551461888287910068240565525 25849776013495784448776509)
            ·
              refine ⟨9693666005060919168291191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25849776013495784448776509 9693666005060919168291191)
              ·
                refine ⟨14540499007591378752436787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9693666005060919168291191 14540499007591378752436787)
                ·
                  refine ⟨21810748511387068128655181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14540499007591378752436787 21810748511387068128655181)
                  ·
                    refine ⟨8179030691770150548245693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21810748511387068128655181 8179030691770150548245693)
                    ·
                      refine ⟨3067136509413806455592135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8179030691770150548245693 3067136509413806455592135)
                      ·
                        rfl

theorem cell23_5973227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 1, 1, 3, 3].length) (baseStart_5973227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5973227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5973227 prefixEnd_5973227 := by exact prefixLift 5973227
  have htrace : WordTrace (prefixWord ++ tailWord_5973227) baseStart_5973227 baseEnd_5973227 := by
    simpa [prefixWord, tailWord_5973227, baseEnd_5973227] using wordTrace_append hprefix tailTrace_5973227
  have hstable : (prefixWord ++ tailWord_5973227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5973227).length < 2 ^ (prefixWord ++ tailWord_5973227).sum := by decide
  have hdescent : baseEnd_5973227 < baseStart_5973227 := by decide
  rcases family_descends (prefixWord ++ tailWord_5973227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5973230 : List Nat := [4, 1, 2, 1, 1, 1, 2, 2, 2, 7]
def baseStart_5973230 : Nat := 118140960795 + 5973230 * 2 ^ 59
def prefixEnd_5973230 : Nat := 4983230072969 + 3 ^ 40 * 5973230 * 2
def baseEnd_5973230 : Nat := 1022379349951923314618207

theorem tailTrace_5973230 : CollatzResearch.WordTrace tailWord_5973230 prefixEnd_5973230 1022379349951923314618207 := by
  unfold tailWord_5973230
  simp only [CollatzResearch.WordTrace]
  refine ⟨27232699518751916413887643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145241064100010220874067429 27232699518751916413887643)
  ·
    refine ⟨40849049278127874620831465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27232699518751916413887643 40849049278127874620831465)
    ·
      refine ⟨30636786958595905965623599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40849049278127874620831465 30636786958595905965623599)
      ·
        refine ⟨45955180437893858948435399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30636786958595905965623599 45955180437893858948435399)
        ·
          refine ⟨68932770656840788422653099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45955180437893858948435399 68932770656840788422653099)
          ·
            refine ⟨103399155985261182633979649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68932770656840788422653099 103399155985261182633979649)
            ·
              refine ⟨77549366988945886975484737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103399155985261182633979649 77549366988945886975484737)
              ·
                refine ⟨58162025241709415231613553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77549366988945886975484737 58162025241709415231613553)
                ·
                  refine ⟨43621518931282061423710165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58162025241709415231613553 43621518931282061423710165)
                  ·
                    refine ⟨1022379349951923314618207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43621518931282061423710165 1022379349951923314618207)
                    ·
                      rfl

theorem cell23_5973230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_5973230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5973230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5973230 prefixEnd_5973230 := by exact prefixLift 5973230
  have htrace : WordTrace (prefixWord ++ tailWord_5973230) baseStart_5973230 baseEnd_5973230 := by
    simpa [prefixWord, tailWord_5973230, baseEnd_5973230] using wordTrace_append hprefix tailTrace_5973230
  have hstable : (prefixWord ++ tailWord_5973230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5973230).length < 2 ^ (prefixWord ++ tailWord_5973230).sum := by decide
  have hdescent : baseEnd_5973230 < baseStart_5973230 := by decide
  rcases family_descends (prefixWord ++ tailWord_5973230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5973234 : List Nat := [3, 2, 1, 3, 3, 2, 2, 7]
def baseStart_5973234 : Nat := 118140960795 + 5973234 * 2 ^ 59
def prefixEnd_5973234 : Nat := 4983230072969 + 3 ^ 40 * 5973234 * 2
def baseEnd_5973234 : Nat := 113597781621421775118689

theorem tailTrace_5973234 : CollatzResearch.WordTrace tailWord_5973234 prefixEnd_5973234 113597781621421775118689 := by
  unfold tailWord_5973234
  simp only [CollatzResearch.WordTrace]
  refine ⟨54465435510500209998561689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145241161361333893329497837 54465435510500209998561689)
  ·
    refine ⟨40849076632875157498921267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54465435510500209998561689 40849076632875157498921267)
    ·
      refine ⟨61273614949312736248381901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40849076632875157498921267 61273614949312736248381901)
      ·
        refine ⟨22977605605992276093143213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61273614949312736248381901 22977605605992276093143213)
        ·
          refine ⟨8616602102247103534928705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22977605605992276093143213 8616602102247103534928705)
          ·
            refine ⟨6462451576685327651196529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8616602102247103534928705 6462451576685327651196529)
            ·
              refine ⟨4846838682513995738397397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6462451576685327651196529 4846838682513995738397397)
              ·
                refine ⟨113597781621421775118689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4846838682513995738397397 113597781621421775118689)
                ·
                  rfl

theorem cell23_5973234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2, 7].length) (baseStart_5973234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5973234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5973234 prefixEnd_5973234 := by exact prefixLift 5973234
  have htrace : WordTrace (prefixWord ++ tailWord_5973234) baseStart_5973234 baseEnd_5973234 := by
    simpa [prefixWord, tailWord_5973234, baseEnd_5973234] using wordTrace_append hprefix tailTrace_5973234
  have hstable : (prefixWord ++ tailWord_5973234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5973234).length < 2 ^ (prefixWord ++ tailWord_5973234).sum := by decide
  have hdescent : baseEnd_5973234 < baseStart_5973234 := by decide
  rcases family_descends (prefixWord ++ tailWord_5973234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5973284 : List Nat := [2, 3, 1, 3, 1, 1, 2, 3, 1, 4, 2]
def baseStart_5973284 : Nat := 118140960795 + 5973284 * 2 ^ 59
def prefixEnd_5973284 : Nat := 4983230072969 + 3 ^ 40 * 5973284 * 2
def baseEnd_5973284 : Nat := 3067165777811112732579373

theorem tailTrace_5973284 : CollatzResearch.WordTrace tailWord_5973284 prefixEnd_5973284 3067165777811112732579373 := by
  unfold tailWord_5973284
  simp only [CollatzResearch.WordTrace]
  refine ⟨108931782845909849266783453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145242377127879799022377937 108931782845909849266783453)
  ·
    refine ⟨40849418567216193475043795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108931782845909849266783453 40849418567216193475043795)
    ·
      refine ⟨61274127850824290212565693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40849418567216193475043795 61274127850824290212565693)
      ·
        refine ⟨22977797944059108829712135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61274127850824290212565693 22977797944059108829712135)
        ·
          refine ⟨34466696916088663244568203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22977797944059108829712135 34466696916088663244568203)
          ·
            refine ⟨51700045374132994866852305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34466696916088663244568203 51700045374132994866852305)
            ·
              refine ⟨38775034030599746150139229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51700045374132994866852305 38775034030599746150139229)
              ·
                refine ⟨14540637761474904806302211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38775034030599746150139229 14540637761474904806302211)
                ·
                  refine ⟨21810956642212357209453317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14540637761474904806302211 21810956642212357209453317)
                  ·
                    refine ⟨4089554370414816976772497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21810956642212357209453317 4089554370414816976772497)
                    ·
                      refine ⟨3067165777811112732579373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4089554370414816976772497 3067165777811112732579373)
                      ·
                        rfl

theorem cell23_5973284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_5973284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5973284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5973284 prefixEnd_5973284 := by exact prefixLift 5973284
  have htrace : WordTrace (prefixWord ++ tailWord_5973284) baseStart_5973284 baseEnd_5973284 := by
    simpa [prefixWord, tailWord_5973284, baseEnd_5973284] using wordTrace_append hprefix tailTrace_5973284
  have hstable : (prefixWord ++ tailWord_5973284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5973284).length < 2 ^ (prefixWord ++ tailWord_5973284).sum := by decide
  have hdescent : baseEnd_5973284 < baseStart_5973284 := by decide
  rcases family_descends (prefixWord ++ tailWord_5973284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5973288 : List Nat := [2, 1, 5, 1, 2, 3, 1, 2, 1, 3, 2]
def baseStart_5973288 : Nat := 118140960795 + 5973288 * 2 ^ 59
def prefixEnd_5973288 : Nat := 4983230072969 + 3 ^ 40 * 5973288 * 2
def baseEnd_5973288 : Nat := 3067167831733730716929355

theorem tailTrace_5973288 : CollatzResearch.WordTrace tailWord_5973288 prefixEnd_5973288 3067167831733730716929355 := by
  unfold tailWord_5973288
  simp only [CollatzResearch.WordTrace]
  refine ⟨108931855791902603608356259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145242474389203471477808345 108931855791902603608356259)
  ·
    refine ⟨163397783687853905412534389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108931855791902603608356259 163397783687853905412534389)
    ·
      refine ⟨15318542220736303632425099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 163397783687853905412534389 15318542220736303632425099)
      ·
        refine ⟨22977813331104455448637649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15318542220736303632425099 22977813331104455448637649)
        ·
          refine ⟨17233359998328341586478237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22977813331104455448637649 17233359998328341586478237)
          ·
            refine ⟨6462509999373128094929339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17233359998328341586478237 6462509999373128094929339)
            ·
              refine ⟨9693764999059692142394009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6462509999373128094929339 9693764999059692142394009)
              ·
                refine ⟨7270323749294769106795507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9693764999059692142394009 7270323749294769106795507)
                ·
                  refine ⟨10905485623942153660193261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7270323749294769106795507 10905485623942153660193261)
                  ·
                    refine ⟨4089557108978307622572473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10905485623942153660193261 4089557108978307622572473)
                    ·
                      refine ⟨3067167831733730716929355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4089557108978307622572473 3067167831733730716929355)
                      ·
                        rfl

theorem cell23_5973288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_5973288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5973288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5973288 prefixEnd_5973288 := by exact prefixLift 5973288
  have htrace : WordTrace (prefixWord ++ tailWord_5973288) baseStart_5973288 baseEnd_5973288 := by
    simpa [prefixWord, tailWord_5973288, baseEnd_5973288] using wordTrace_append hprefix tailTrace_5973288
  have hstable : (prefixWord ++ tailWord_5973288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5973288).length < 2 ^ (prefixWord ++ tailWord_5973288).sum := by decide
  have hdescent : baseEnd_5973288 < baseStart_5973288 := by decide
  rcases family_descends (prefixWord ++ tailWord_5973288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5973320 : List Nat := [2, 1, 3, 1, 1, 2, 1, 2, 3, 7]
def baseStart_5973320 : Nat := 118140960795 + 5973320 * 2 ^ 59
def prefixEnd_5973320 : Nat := 4983230072969 + 3 ^ 40 * 5973320 * 2
def baseEnd_5973320 : Nat := 1022394754371558197243069

theorem tailTrace_5973320 : CollatzResearch.WordTrace tailWord_5973320 prefixEnd_5973320 1022394754371558197243069 := by
  unfold tailWord_5973320
  simp only [CollatzResearch.WordTrace]
  refine ⟨108932439359844638340938707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145243252479792851121251609 108932439359844638340938707)
  ·
    refine ⟨163398659039766957511408061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108932439359844638340938707 163398659039766957511408061)
    ·
      refine ⟨61274497139912609066778023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163398659039766957511408061 61274497139912609066778023)
      ·
        refine ⟨91911745709868913600167035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61274497139912609066778023 91911745709868913600167035)
        ·
          refine ⟨137867618564803370400250553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91911745709868913600167035 137867618564803370400250553)
          ·
            refine ⟨103400713923602527800187915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137867618564803370400250553 103400713923602527800187915)
            ·
              refine ⟨155101070885403791700281873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103400713923602527800187915 155101070885403791700281873)
              ·
                refine ⟨116325803164052843775211405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155101070885403791700281873 116325803164052843775211405)
                ·
                  refine ⟨43622176186519816415704277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 116325803164052843775211405 43622176186519816415704277)
                  ·
                    refine ⟨1022394754371558197243069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43622176186519816415704277 1022394754371558197243069)
                    ·
                      rfl

theorem cell23_5973320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 3, 7].length) (baseStart_5973320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5973320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5973320 prefixEnd_5973320 := by exact prefixLift 5973320
  have htrace : WordTrace (prefixWord ++ tailWord_5973320) baseStart_5973320 baseEnd_5973320 := by
    simpa [prefixWord, tailWord_5973320, baseEnd_5973320] using wordTrace_append hprefix tailTrace_5973320
  have hstable : (prefixWord ++ tailWord_5973320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5973320).length < 2 ^ (prefixWord ++ tailWord_5973320).sum := by decide
  have hdescent : baseEnd_5973320 < baseStart_5973320 := by decide
  rcases family_descends (prefixWord ++ tailWord_5973320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5973324 : List Nat := [2, 2, 1, 3, 2, 3, 1, 4, 5]
def baseStart_5973324 : Nat := 118140960795 + 5973324 * 2 ^ 59
def prefixEnd_5973324 : Nat := 4983230072969 + 3 ^ 40 * 5973324 * 2
def baseEnd_5973324 : Nat := 340798479670810286231021

theorem tailTrace_5973324 : CollatzResearch.WordTrace tailWord_5973324 prefixEnd_5973324 340798479670810286231021 := by
  unfold tailWord_5973324
  simp only [CollatzResearch.WordTrace]
  refine ⟨108932512305837392682511513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145243349741116523576682017 108932512305837392682511513)
  ·
    refine ⟨81699384229378044511883635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108932512305837392682511513 81699384229378044511883635)
    ·
      refine ⟨122549076344067066767825453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81699384229378044511883635 122549076344067066767825453)
      ·
        refine ⟨45955903629025150037934545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122549076344067066767825453 45955903629025150037934545)
        ·
          refine ⟨34466927721768862528450909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45955903629025150037934545 34466927721768862528450909)
          ·
            refine ⟨12925097895663323448169091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34466927721768862528450909 12925097895663323448169091)
            ·
              refine ⟨19387646843494985172253637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12925097895663323448169091 19387646843494985172253637)
              ·
                refine ⟨3635183783155309719797557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19387646843494985172253637 3635183783155309719797557)
                ·
                  refine ⟨340798479670810286231021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3635183783155309719797557 340798479670810286231021)
                  ·
                    rfl

theorem cell23_5973324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 4, 5].length) (baseStart_5973324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5973324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5973324 prefixEnd_5973324 := by exact prefixLift 5973324
  have htrace : WordTrace (prefixWord ++ tailWord_5973324) baseStart_5973324 baseEnd_5973324 := by
    simpa [prefixWord, tailWord_5973324, baseEnd_5973324] using wordTrace_append hprefix tailTrace_5973324
  have hstable : (prefixWord ++ tailWord_5973324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5973324).length < 2 ^ (prefixWord ++ tailWord_5973324).sum := by decide
  have hdescent : baseEnd_5973324 < baseStart_5973324 := by decide
  rcases family_descends (prefixWord ++ tailWord_5973324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5973354 : List Nat := [3, 1, 3, 3, 2, 1, 1, 1, 1, 7]
def baseStart_5973354 : Nat := 118140960795 + 5973354 * 2 ^ 59
def prefixEnd_5973354 : Nat := 4983230072969 + 3 ^ 40 * 5973354 * 2
def baseEnd_5973354 : Nat := 1022400573818975819568017

theorem tailTrace_5973354 : CollatzResearch.WordTrace tailWord_5973354 prefixEnd_5973354 1022400573818975819568017 := by
  unfold tailWord_5973354
  simp only [CollatzResearch.WordTrace]
  refine ⟨54466529700391525122153779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145244079201044066992410077 54466529700391525122153779)
  ·
    refine ⟨81699794550587287683230669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54466529700391525122153779 81699794550587287683230669)
    ·
      refine ⟨30637422956470232881211501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81699794550587287683230669 30637422956470232881211501)
      ·
        refine ⟨11489033608676337330454313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30637422956470232881211501 11489033608676337330454313)
        ·
          refine ⟨8616775206507252997840735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11489033608676337330454313 8616775206507252997840735)
          ·
            refine ⟨12925162809760879496761103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8616775206507252997840735 12925162809760879496761103)
            ·
              refine ⟨19387744214641319245141655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12925162809760879496761103 19387744214641319245141655)
              ·
                refine ⟨29081616321961978867712483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19387744214641319245141655 29081616321961978867712483)
                ·
                  refine ⟨43622424482942968301568725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29081616321961978867712483 43622424482942968301568725)
                  ·
                    refine ⟨1022400573818975819568017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43622424482942968301568725 1022400573818975819568017)
                    ·
                      rfl

theorem cell23_5973354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_5973354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5973354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5973354 prefixEnd_5973354 := by exact prefixLift 5973354
  have htrace : WordTrace (prefixWord ++ tailWord_5973354) baseStart_5973354 baseEnd_5973354 := by
    simpa [prefixWord, tailWord_5973354, baseEnd_5973354] using wordTrace_append hprefix tailTrace_5973354
  have hstable : (prefixWord ++ tailWord_5973354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5973354).length < 2 ^ (prefixWord ++ tailWord_5973354).sum := by decide
  have hdescent : baseEnd_5973354 < baseStart_5973354 := by decide
  rcases family_descends (prefixWord ++ tailWord_5973354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5973358 : List Nat := [4, 1, 2, 4, 1, 1, 2, 3, 5]
def baseStart_5973358 : Nat := 118140960795 + 5973358 * 2 ^ 59
def prefixEnd_5973358 : Nat := 4983230072969 + 3 ^ 40 * 5973358 * 2
def baseEnd_5973358 : Nat := 340800419486616160339337

theorem tailTrace_5973358 : CollatzResearch.WordTrace tailWord_5973358 prefixEnd_5973358 340800419486616160339337 := by
  unfold tailWord_5973358
  simp only [CollatzResearch.WordTrace]
  refine ⟨27233283086693951146470091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145244176462367739447840485 27233283086693951146470091)
  ·
    refine ⟨40849924630040926719705137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27233283086693951146470091 40849924630040926719705137)
    ·
      refine ⟨30637443472530695039778853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40849924630040926719705137 30637443472530695039778853)
      ·
        refine ⟨5744520651099505319958535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30637443472530695039778853 5744520651099505319958535)
        ·
          refine ⟨8616780976649257979937803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5744520651099505319958535 8616780976649257979937803)
          ·
            refine ⟨12925171464973886969906705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8616780976649257979937803 12925171464973886969906705)
            ·
              refine ⟨9693878598730415227430029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12925171464973886969906705 9693878598730415227430029)
              ·
                refine ⟨3635204474523905710286261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9693878598730415227430029 3635204474523905710286261)
                ·
                  refine ⟨340800419486616160339337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3635204474523905710286261 340800419486616160339337)
                  ·
                    rfl

theorem cell23_5973358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 3, 5].length) (baseStart_5973358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5973358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5973358 prefixEnd_5973358 := by exact prefixLift 5973358
  have htrace : WordTrace (prefixWord ++ tailWord_5973358) baseStart_5973358 baseEnd_5973358 := by
    simpa [prefixWord, tailWord_5973358, baseEnd_5973358] using wordTrace_append hprefix tailTrace_5973358
  have hstable : (prefixWord ++ tailWord_5973358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5973358).length < 2 ^ (prefixWord ++ tailWord_5973358).sum := by decide
  have hdescent : baseEnd_5973358 < baseStart_5973358 := by decide
  rcases family_descends (prefixWord ++ tailWord_5973358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5973367 : List Nat := [1, 1, 3, 1, 1, 2, 3, 2, 5, 4]
def baseStart_5973367 : Nat := 118140960795 + 5973367 * 2 ^ 59
def prefixEnd_5973367 : Nat := 4983230072969 + 3 ^ 40 * 5973367 * 2
def baseEnd_5973367 : Nat := 1022402798901811969280497

theorem tailTrace_5973367 : CollatzResearch.WordTrace tailWord_5973367 prefixEnd_5973367 1022402798901811969280497 := by
  unfold tailWord_5973367
  simp only [CollatzResearch.WordTrace]
  refine ⟨217866592950519003708838355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145244395300346002472558903 217866592950519003708838355)
  ·
    refine ⟨326799889425778505563257533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217866592950519003708838355 326799889425778505563257533)
    ·
      refine ⟨122549958534666939586221575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 326799889425778505563257533 122549958534666939586221575)
      ·
        refine ⟨183824937802000409379332363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122549958534666939586221575 183824937802000409379332363)
        ·
          refine ⟨275737406703000614068998545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183824937802000409379332363 275737406703000614068998545)
          ·
            refine ⟨206803055027250460551748909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 275737406703000614068998545 206803055027250460551748909)
            ·
              refine ⟨77551145635218922706905841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 206803055027250460551748909 77551145635218922706905841)
              ·
                refine ⟨58163359226414192030179381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77551145635218922706905841 58163359226414192030179381)
                ·
                  refine ⟨5452814927476330502829317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58163359226414192030179381 5452814927476330502829317)
                  ·
                    refine ⟨1022402798901811969280497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5452814927476330502829317 1022402798901811969280497)
                    ·
                      rfl

theorem cell23_5973367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 5, 4].length) (baseStart_5973367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5973367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5973367 prefixEnd_5973367 := by exact prefixLift 5973367
  have htrace : WordTrace (prefixWord ++ tailWord_5973367) baseStart_5973367 baseEnd_5973367 := by
    simpa [prefixWord, tailWord_5973367, baseEnd_5973367] using wordTrace_append hprefix tailTrace_5973367
  have hstable : (prefixWord ++ tailWord_5973367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5973367).length < 2 ^ (prefixWord ++ tailWord_5973367).sum := by decide
  have hdescent : baseEnd_5973367 < baseStart_5973367 := by decide
  rcases family_descends (prefixWord ++ tailWord_5973367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5973384 : List Nat := [2, 1, 3, 3, 1, 2, 1, 3, 3, 4]
def baseStart_5973384 : Nat := 118140960795 + 5973384 * 2 ^ 59
def prefixEnd_5973384 : Nat := 4983230072969 + 3 ^ 40 * 5973384 * 2
def baseEnd_5973384 : Nat := 1022405708625520780442971

theorem tailTrace_5973384 : CollatzResearch.WordTrace tailWord_5973384 prefixEnd_5973384 1022405708625520780442971 := by
  unfold tailWord_5973384
  simp only [CollatzResearch.WordTrace]
  refine ⟨108933606495728707806103603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145244808660971610408138137 108933606495728707806103603)
  ·
    refine ⟨163400409743593061709155405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108933606495728707806103603 163400409743593061709155405)
    ·
      refine ⟨61275153653847398140933277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163400409743593061709155405 61275153653847398140933277)
      ·
        refine ⟨22978182620192774302849979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61275153653847398140933277 22978182620192774302849979)
        ·
          refine ⟨34467273930289161454274969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22978182620192774302849979 34467273930289161454274969)
          ·
            refine ⟨25850455447716871090706227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34467273930289161454274969 25850455447716871090706227)
            ·
              refine ⟨38775683171575306636059341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25850455447716871090706227 38775683171575306636059341)
              ·
                refine ⟨14540881189340739988522253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38775683171575306636059341 14540881189340739988522253)
                ·
                  refine ⟨5452830446002777495695845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14540881189340739988522253 5452830446002777495695845)
                  ·
                    refine ⟨1022405708625520780442971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5452830446002777495695845 1022405708625520780442971)
                    ·
                      rfl

theorem cell23_5973384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 3, 3, 4].length) (baseStart_5973384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5973384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5973384 prefixEnd_5973384 := by exact prefixLift 5973384
  have htrace : WordTrace (prefixWord ++ tailWord_5973384) baseStart_5973384 baseEnd_5973384 := by
    simpa [prefixWord, tailWord_5973384, baseEnd_5973384] using wordTrace_append hprefix tailTrace_5973384
  have hstable : (prefixWord ++ tailWord_5973384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5973384).length < 2 ^ (prefixWord ++ tailWord_5973384).sum := by decide
  have hdescent : baseEnd_5973384 < baseStart_5973384 := by decide
  rcases family_descends (prefixWord ++ tailWord_5973384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5973397 : List Nat := [1, 3, 2, 1, 1, 2, 2, 5, 6]
def baseStart_5973397 : Nat := 118140960795 + 5973397 * 2 ^ 59
def prefixEnd_5973397 : Nat := 4983230072969 + 3 ^ 40 * 5973397 * 2
def baseEnd_5973397 : Nat := 340802644569452310051817

theorem tailTrace_5973397 : CollatzResearch.WordTrace tailWord_5973397 prefixEnd_5973397 340802644569452310051817 := by
  unfold tailWord_5973397
  simp only [CollatzResearch.WordTrace]
  refine ⟨217867687140410318832430445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145245124760273545888286963 217867687140410318832430445)
  ·
    refine ⟨81700382677653869562161417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217867687140410318832430445 81700382677653869562161417)
    ·
      refine ⟨61275287008240402171621063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81700382677653869562161417 61275287008240402171621063)
      ·
        refine ⟨91912930512360603257431595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61275287008240402171621063 91912930512360603257431595)
        ·
          refine ⟨137869395768540904886147393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91912930512360603257431595 137869395768540904886147393)
          ·
            refine ⟨103402046826405678664610545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137869395768540904886147393 103402046826405678664610545)
            ·
              refine ⟨77551535119804258998457909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103402046826405678664610545 77551535119804258998457909)
              ·
                refine ⟨7270456417481649281105429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77551535119804258998457909 7270456417481649281105429)
                ·
                  refine ⟨340802644569452310051817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7270456417481649281105429 340802644569452310051817)
                  ·
                    rfl

theorem cell23_5973397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 5, 6].length) (baseStart_5973397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5973397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5973397 prefixEnd_5973397 := by exact prefixLift 5973397
  have htrace : WordTrace (prefixWord ++ tailWord_5973397) baseStart_5973397 baseEnd_5973397 := by
    simpa [prefixWord, tailWord_5973397, baseEnd_5973397] using wordTrace_append hprefix tailTrace_5973397
  have hstable : (prefixWord ++ tailWord_5973397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5973397).length < 2 ^ (prefixWord ++ tailWord_5973397).sum := by decide
  have hdescent : baseEnd_5973397 < baseStart_5973397 := by decide
  rcases family_descends (prefixWord ++ tailWord_5973397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5973464 : List Nat := [2, 1, 2, 2, 2, 1, 2, 1, 2, 6, 2]
def baseStart_5973464 : Nat := 118140960795 + 5973464 * 2 ^ 59
def prefixEnd_5973464 : Nat := 4983230072969 + 3 ^ 40 * 5973464 * 2
def baseEnd_5973464 : Nat := 3067258204328922028328545

theorem tailTrace_5973464 : CollatzResearch.WordTrace tailWord_5973464 prefixEnd_5973464 3067258204328922028328545 := by
  unfold tailWord_5973464
  simp only [CollatzResearch.WordTrace]
  refine ⟨108935065415583794637559723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145246753887445059516746297 108935065415583794637559723)
  ·
    refine ⟨163402598123375691956339585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108935065415583794637559723 163402598123375691956339585)
    ·
      refine ⟨122551948592531768967254689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163402598123375691956339585 122551948592531768967254689)
      ·
        refine ⟨91913961444398826725441017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122551948592531768967254689 91913961444398826725441017)
        ·
          refine ⟨68935471083299120044080763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91913961444398826725441017 68935471083299120044080763)
          ·
            refine ⟨103403206624948680066121145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68935471083299120044080763 103403206624948680066121145)
            ·
              refine ⟨77552404968711510049590859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103403206624948680066121145 77552404968711510049590859)
              ·
                refine ⟨116328607453067265074386289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77552404968711510049590859 116328607453067265074386289)
                ·
                  refine ⟨87246455589800448805789717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116328607453067265074386289 87246455589800448805789717)
                  ·
                    refine ⟨4089677605771896037771393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 87246455589800448805789717 4089677605771896037771393)
                    ·
                      refine ⟨3067258204328922028328545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4089677605771896037771393 3067258204328922028328545)
                      ·
                        rfl

theorem cell23_5973464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 6, 2].length) (baseStart_5973464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5973464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5973464 prefixEnd_5973464 := by exact prefixLift 5973464
  have htrace : WordTrace (prefixWord ++ tailWord_5973464) baseStart_5973464 baseEnd_5973464 := by
    simpa [prefixWord, tailWord_5973464, baseEnd_5973464] using wordTrace_append hprefix tailTrace_5973464
  have hstable : (prefixWord ++ tailWord_5973464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5973464).length < 2 ^ (prefixWord ++ tailWord_5973464).sum := by decide
  have hdescent : baseEnd_5973464 < baseStart_5973464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5973464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5973467 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 3, 8, 3]
def baseStart_5973467 : Nat := 118140960795 + 5973467 * 2 ^ 59
def prefixEnd_5973467 : Nat := 4983230072969 + 3 ^ 40 * 5973467 * 2
def baseEnd_5973467 : Nat := 3067259744770885516591031

theorem tailTrace_5973467 : CollatzResearch.WordTrace tailWord_5973467 prefixEnd_5973467 3067259744770885516591031 := by
  unfold tailWord_5973467
  simp only [CollatzResearch.WordTrace]
  refine ⟨217870240250156720787478655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145246826833437813858319103 217870240250156720787478655)
  ·
    refine ⟨326805360375235081181217983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217870240250156720787478655 326805360375235081181217983)
    ·
      refine ⟨490208040562852621771826975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326805360375235081181217983 490208040562852621771826975)
      ·
        refine ⟨735312060844278932657740463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 490208040562852621771826975 735312060844278932657740463)
        ·
          refine ⟨1102968091266418398986610695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 735312060844278932657740463 1102968091266418398986610695)
          ·
            refine ⟨1654452136899627598479916043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1102968091266418398986610695 1654452136899627598479916043)
            ·
              refine ⟨2481678205349441397719874065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1654452136899627598479916043 2481678205349441397719874065)
              ·
                refine ⟨1861258654012081048289905549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2481678205349441397719874065 1861258654012081048289905549)
                ·
                  refine ⟨697971995254530393108714581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1861258654012081048289905549 697971995254530393108714581)
                  ·
                    refine ⟨8179359319389028044242749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 697971995254530393108714581 8179359319389028044242749)
                    ·
                      refine ⟨3067259744770885516591031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8179359319389028044242749 3067259744770885516591031)
                      ·
                        rfl

theorem cell23_5973467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8, 3].length) (baseStart_5973467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5973467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5973467 prefixEnd_5973467 := by exact prefixLift 5973467
  have htrace : WordTrace (prefixWord ++ tailWord_5973467) baseStart_5973467 baseEnd_5973467 := by
    simpa [prefixWord, tailWord_5973467, baseEnd_5973467] using wordTrace_append hprefix tailTrace_5973467
  have hstable : (prefixWord ++ tailWord_5973467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5973467).length < 2 ^ (prefixWord ++ tailWord_5973467).sum := by decide
  have hdescent : baseEnd_5973467 < baseStart_5973467 := by decide
  rcases family_descends (prefixWord ++ tailWord_5973467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5973511 : List Nat := [1, 1, 4, 3, 2, 2, 2, 1, 1, 2, 4]
def baseStart_5973511 : Nat := 118140960795 + 5973511 * 2 ^ 59
def prefixEnd_5973511 : Nat := 4983230072969 + 3 ^ 40 * 5973511 * 2
def baseEnd_5973511 : Nat := 3067282337919683344440829

theorem tailTrace_5973511 : CollatzResearch.WordTrace tailWord_5973511 prefixEnd_5973511 3067282337919683344440829 := by
  unfold tailWord_5973511
  simp only [CollatzResearch.WordTrace]
  refine ⟨217871845061997316302080387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145247896707998210868053591 217871845061997316302080387)
  ·
    refine ⟨326807767592995974453120581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217871845061997316302080387 326807767592995974453120581)
    ·
      refine ⟨61276456423686745209960109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 326807767592995974453120581 61276456423686745209960109)
      ·
        refine ⟨22978671158882529453735041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61276456423686745209960109 22978671158882529453735041)
        ·
          refine ⟨17234003369161897090301281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22978671158882529453735041 17234003369161897090301281)
          ·
            refine ⟨12925502526871422817725961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17234003369161897090301281 12925502526871422817725961)
            ·
              refine ⟨9694126895153567113294471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12925502526871422817725961 9694126895153567113294471)
              ·
                refine ⟨14541190342730350669941707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9694126895153567113294471 14541190342730350669941707)
                ·
                  refine ⟨21811785514095526004912561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14541190342730350669941707 21811785514095526004912561)
                  ·
                    refine ⟨16358839135571644503684421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21811785514095526004912561 16358839135571644503684421)
                    ·
                      refine ⟨3067282337919683344440829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16358839135571644503684421 3067282337919683344440829)
                      ·
                        rfl

theorem cell23_5973511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_5973511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5973511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5973511 prefixEnd_5973511 := by exact prefixLift 5973511
  have htrace : WordTrace (prefixWord ++ tailWord_5973511) baseStart_5973511 baseEnd_5973511 := by
    simpa [prefixWord, tailWord_5973511, baseEnd_5973511] using wordTrace_append hprefix tailTrace_5973511
  have hstable : (prefixWord ++ tailWord_5973511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5973511).length < 2 ^ (prefixWord ++ tailWord_5973511).sum := by decide
  have hdescent : baseEnd_5973511 < baseStart_5973511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5973511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5973565 : List Nat := [1, 4, 1, 3, 4, 1, 1, 1, 1, 3, 3]
def baseStart_5973565 : Nat := 118140960795 + 5973565 * 2 ^ 59
def prefixEnd_5973565 : Nat := 4983230072969 + 3 ^ 40 * 5973565 * 2
def baseEnd_5973565 : Nat := 3067310065875026133165581

theorem tailTrace_5973565 : CollatzResearch.WordTrace tailWord_5973565 prefixEnd_5973565 3067310065875026133165581 := by
  unfold tailWord_5973565
  simp only [CollatzResearch.WordTrace]
  refine ⟨217873814603801683524546149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145249209735867789016364099 217873814603801683524546149)
  ·
    refine ⟨40851340238212815660852403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 217873814603801683524546149 40851340238212815660852403)
    ·
      refine ⟨61277010357319223491278605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40851340238212815660852403 61277010357319223491278605)
      ·
        refine ⟨22978878883994708809229477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61277010357319223491278605 22978878883994708809229477)
        ·
          refine ⟨4308539790749007901730527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22978878883994708809229477 4308539790749007901730527)
          ·
            refine ⟨6462809686123511852595791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4308539790749007901730527 6462809686123511852595791)
            ·
              refine ⟨9694214529185267778893687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6462809686123511852595791 9694214529185267778893687)
              ·
                refine ⟨14541321793777901668340531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9694214529185267778893687 14541321793777901668340531)
                ·
                  refine ⟨21811982690666852502510797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14541321793777901668340531 21811982690666852502510797)
                  ·
                    refine ⟨8179493509000069688441549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21811982690666852502510797 8179493509000069688441549)
                    ·
                      refine ⟨3067310065875026133165581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8179493509000069688441549 3067310065875026133165581)
                      ·
                        rfl

theorem cell23_5973565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_5973565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5973565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5973565 prefixEnd_5973565 := by exact prefixLift 5973565
  have htrace : WordTrace (prefixWord ++ tailWord_5973565) baseStart_5973565 baseEnd_5973565 := by
    simpa [prefixWord, tailWord_5973565, baseEnd_5973565] using wordTrace_append hprefix tailTrace_5973565
  have hstable : (prefixWord ++ tailWord_5973565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5973565).length < 2 ^ (prefixWord ++ tailWord_5973565).sum := by decide
  have hdescent : baseEnd_5973565 < baseStart_5973565 := by decide
  rcases family_descends (prefixWord ++ tailWord_5973565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5973575 : List Nat := [1, 1, 4, 1, 5, 1, 2, 2, 1, 3, 2]
def baseStart_5973575 : Nat := 118140960795 + 5973575 * 2 ^ 59
def prefixEnd_5973575 : Nat := 4983230072969 + 3 ^ 40 * 5973575 * 2
def baseEnd_5973575 : Nat := 3067315200681571094040535

theorem tailTrace_5973575 : CollatzResearch.WordTrace tailWord_5973575 prefixEnd_5973575 3067315200681571094040535 := by
  unfold tailWord_5973575
  simp only [CollatzResearch.WordTrace]
  refine ⟨217874179333765455232410179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145249452889176970154940119 217874179333765455232410179)
  ·
    refine ⟨326811269000648182848615269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217874179333765455232410179 326811269000648182848615269)
    ·
      refine ⟨61277112937621534284115363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 326811269000648182848615269 61277112937621534284115363)
      ·
        refine ⟨91915669406432301426173045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61277112937621534284115363 91915669406432301426173045)
        ·
          refine ⟨8617094006853028258703723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 91915669406432301426173045 8617094006853028258703723)
          ·
            refine ⟨12925641010279542388055585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8617094006853028258703723 12925641010279542388055585)
            ·
              refine ⟨9694230757709656791041689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12925641010279542388055585 9694230757709656791041689)
              ·
                refine ⟨7270673068282242593281267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9694230757709656791041689 7270673068282242593281267)
                ·
                  refine ⟨10906009602423363889921901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7270673068282242593281267 10906009602423363889921901)
                  ·
                    refine ⟨4089753600908761458720713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10906009602423363889921901 4089753600908761458720713)
                    ·
                      refine ⟨3067315200681571094040535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4089753600908761458720713 3067315200681571094040535)
                      ·
                        rfl

theorem cell23_5973575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 2, 1, 3, 2].length) (baseStart_5973575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5973575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5973575 prefixEnd_5973575 := by exact prefixLift 5973575
  have htrace : WordTrace (prefixWord ++ tailWord_5973575) baseStart_5973575 baseEnd_5973575 := by
    simpa [prefixWord, tailWord_5973575, baseEnd_5973575] using wordTrace_append hprefix tailTrace_5973575
  have hstable : (prefixWord ++ tailWord_5973575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5973575).length < 2 ^ (prefixWord ++ tailWord_5973575).sum := by decide
  have hdescent : baseEnd_5973575 < baseStart_5973575 := by decide
  rcases family_descends (prefixWord ++ tailWord_5973575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5973588 : List Nat := [2, 4, 1, 1, 1, 2, 1, 1, 6, 2, 2]
def baseStart_5973588 : Nat := 118140960795 + 5973588 * 2 ^ 59
def prefixEnd_5973588 : Nat := 4983230072969 + 3 ^ 40 * 5973588 * 2
def baseEnd_5973588 : Nat := 3067321875930079543177975

theorem tailTrace_5973588 : CollatzResearch.WordTrace tailWord_5973588 prefixEnd_5973588 3067321875930079543177975 := by
  unfold tailWord_5973588
  simp only [CollatzResearch.WordTrace]
  refine ⟨108937326741359179226316709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145249768988478905635088945 108937326741359179226316709)
  ·
    refine ⟨20425748764004846104934383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108937326741359179226316709 20425748764004846104934383)
    ·
      refine ⟨30638623146007269157401575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20425748764004846104934383 30638623146007269157401575)
      ·
        refine ⟨45957934719010903736102363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30638623146007269157401575 45957934719010903736102363)
        ·
          refine ⟨68936902078516355604153545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45957934719010903736102363 68936902078516355604153545)
          ·
            refine ⟨51702676558887266703115159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68936902078516355604153545 51702676558887266703115159)
            ·
              refine ⟨77554014838330900054672739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51702676558887266703115159 77554014838330900054672739)
              ·
                refine ⟨116331022257496350082009109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77554014838330900054672739 116331022257496350082009109)
                ·
                  refine ⟨5453016668320141410094177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 116331022257496350082009109 5453016668320141410094177)
                  ·
                    refine ⟨4089762501240106057570633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5453016668320141410094177 4089762501240106057570633)
                    ·
                      refine ⟨3067321875930079543177975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4089762501240106057570633 3067321875930079543177975)
                      ·
                        rfl

theorem cell23_5973588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 6, 2, 2].length) (baseStart_5973588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5973588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5973588 prefixEnd_5973588 := by exact prefixLift 5973588
  have htrace : WordTrace (prefixWord ++ tailWord_5973588) baseStart_5973588 baseEnd_5973588 := by
    simpa [prefixWord, tailWord_5973588, baseEnd_5973588] using wordTrace_append hprefix tailTrace_5973588
  have hstable : (prefixWord ++ tailWord_5973588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5973588).length < 2 ^ (prefixWord ++ tailWord_5973588).sum := by decide
  have hdescent : baseEnd_5973588 < baseStart_5973588 := by decide
  rcases family_descends (prefixWord ++ tailWord_5973588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5973622 : List Nat := [5, 1, 1, 2, 2, 2, 1, 3, 2, 2, 2]
def baseStart_5973622 : Nat := 118140960795 + 5973622 * 2 ^ 59
def prefixEnd_5973622 : Nat := 4983230072969 + 3 ^ 40 * 5973622 * 2
def baseEnd_5973622 : Nat := 3067339334272332410152819

theorem tailTrace_5973622 : CollatzResearch.WordTrace tailWord_5973622 prefixEnd_5973622 3067339334272332410152819 := by
  unfold tailWord_5973622
  simp only [CollatzResearch.WordTrace]
  refine ⟨13617243347787198891210695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145250595709730121506247413 13617243347787198891210695)
  ·
    refine ⟨20425865021680798336816043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13617243347787198891210695 20425865021680798336816043)
    ·
      refine ⟨30638797532521197505224065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20425865021680798336816043 30638797532521197505224065)
      ·
        refine ⟨22979098149390898128918049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30638797532521197505224065 22979098149390898128918049)
        ·
          refine ⟨17234323612043173596688537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22979098149390898128918049 17234323612043173596688537)
          ·
            refine ⟨12925742709032380197516403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17234323612043173596688537 12925742709032380197516403)
            ·
              refine ⟨19388614063548570296274605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12925742709032380197516403 19388614063548570296274605)
              ·
                refine ⟨7270730273830713861102977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19388614063548570296274605 7270730273830713861102977)
                ·
                  refine ⟨5453047705373035395827233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7270730273830713861102977 5453047705373035395827233)
                  ·
                    refine ⟨4089785779029776546870425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5453047705373035395827233 4089785779029776546870425)
                    ·
                      refine ⟨3067339334272332410152819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4089785779029776546870425 3067339334272332410152819)
                      ·
                        rfl

theorem cell23_5973622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_5973622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5973622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5973622 prefixEnd_5973622 := by exact prefixLift 5973622
  have htrace : WordTrace (prefixWord ++ tailWord_5973622) baseStart_5973622 baseEnd_5973622 := by
    simpa [prefixWord, tailWord_5973622, baseEnd_5973622] using wordTrace_append hprefix tailTrace_5973622
  have hstable : (prefixWord ++ tailWord_5973622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5973622).length < 2 ^ (prefixWord ++ tailWord_5973622).sum := by decide
  have hdescent : baseEnd_5973622 < baseStart_5973622 := by decide
  rcases family_descends (prefixWord ++ tailWord_5973622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5973662 : List Nat := [4, 3, 1, 1, 1, 4, 2, 2, 5]
def baseStart_5973662 : Nat := 118140960795 + 5973662 * 2 ^ 59
def prefixEnd_5973662 : Nat := 4983230072969 + 3 ^ 40 * 5973662 * 2
def baseEnd_5973662 : Nat := 340817763722056917072515

theorem tailTrace_5973662 : CollatzResearch.WordTrace tailWord_5973662 prefixEnd_5973662 340817763722056917072515 := by
  unfold tailWord_5973662
  simp only [CollatzResearch.WordTrace]
  refine ⟨27234669060556283636353405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145251568322966846060551493 27234669060556283636353405)
  ·
    refine ⟨10213000897708606363632527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27234669060556283636353405 10213000897708606363632527)
    ·
      refine ⟨15319501346562909545448791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10213000897708606363632527 15319501346562909545448791)
      ·
        refine ⟨22979252019844364318173187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15319501346562909545448791 22979252019844364318173187)
        ·
          refine ⟨34468878029766546477259781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22979252019844364318173187 34468878029766546477259781)
          ·
            refine ⟨6462914630581227464486209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34468878029766546477259781 6462914630581227464486209)
            ·
              refine ⟨4847185972935920598364657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6462914630581227464486209 4847185972935920598364657)
              ·
                refine ⟨3635389479701940448773493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4847185972935920598364657 3635389479701940448773493)
                ·
                  refine ⟨340817763722056917072515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3635389479701940448773493 340817763722056917072515)
                  ·
                    rfl

theorem cell23_5973662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_5973662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5973662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5973662 prefixEnd_5973662 := by exact prefixLift 5973662
  have htrace : WordTrace (prefixWord ++ tailWord_5973662) baseStart_5973662 baseEnd_5973662 := by
    simpa [prefixWord, tailWord_5973662, baseEnd_5973662] using wordTrace_append hprefix tailTrace_5973662
  have hstable : (prefixWord ++ tailWord_5973662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5973662).length < 2 ^ (prefixWord ++ tailWord_5973662).sum := by decide
  have hdescent : baseEnd_5973662 < baseStart_5973662 := by decide
  rcases family_descends (prefixWord ++ tailWord_5973662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5973672 : List Nat := [2, 1, 7, 1, 1, 1, 1, 1, 2, 3, 3]
def baseStart_5973672 : Nat := 118140960795 + 5973672 * 2 ^ 59
def prefixEnd_5973672 : Nat := 4983230072969 + 3 ^ 40 * 5973672 * 2
def baseEnd_5973672 : Nat := 3067365008305057214527589

theorem tailTrace_5973672 : CollatzResearch.WordTrace tailWord_5973672 prefixEnd_5973672 3067365008305057214527589 := by
  unfold tailWord_5973672
  simp only [CollatzResearch.WordTrace]
  refine ⟨108938858607207020399345635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145251811476276027199127513 108938858607207020399345635)
  ·
    refine ⟨163408287910810530599018453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108938858607207020399345635 163408287910810530599018453)
    ·
      refine ⟨3829881747909621810914495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 163408287910810530599018453 3829881747909621810914495)
      ·
        refine ⟨5744822621864432716371743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3829881747909621810914495 5744822621864432716371743)
        ·
          refine ⟨8617233932796649074557615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5744822621864432716371743 8617233932796649074557615)
          ·
            refine ⟨12925850899194973611836423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8617233932796649074557615 12925850899194973611836423)
            ·
              refine ⟨19388776348792460417754635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12925850899194973611836423 19388776348792460417754635)
              ·
                refine ⟨29083164523188690626631953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19388776348792460417754635 29083164523188690626631953)
                ·
                  refine ⟨21812373392391517969973965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29083164523188690626631953 21812373392391517969973965)
                  ·
                    refine ⟨8179640022146819238740237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21812373392391517969973965 8179640022146819238740237)
                    ·
                      refine ⟨3067365008305057214527589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8179640022146819238740237 3067365008305057214527589)
                      ·
                        rfl

theorem cell23_5973672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_5973672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5973672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5973672 prefixEnd_5973672 := by exact prefixLift 5973672
  have htrace : WordTrace (prefixWord ++ tailWord_5973672) baseStart_5973672 baseEnd_5973672 := by
    simpa [prefixWord, tailWord_5973672, baseEnd_5973672] using wordTrace_append hprefix tailTrace_5973672
  have hstable : (prefixWord ++ tailWord_5973672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5973672).length < 2 ^ (prefixWord ++ tailWord_5973672).sum := by decide
  have hdescent : baseEnd_5973672 < baseStart_5973672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5973672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5973728 : List Nat := [2, 1, 1, 3, 1, 2, 3, 3, 3, 1, 3]
def baseStart_5973728 : Nat := 118140960795 + 5973728 * 2 ^ 59
def prefixEnd_5973728 : Nat := 4983230072969 + 3 ^ 40 * 5973728 * 2
def baseEnd_5973728 : Nat := 3067393763221708995427331

theorem tailTrace_5973728 : CollatzResearch.WordTrace tailWord_5973728 prefixEnd_5973728 3067393763221708995427331 := by
  unfold tailWord_5973728
  simp only [CollatzResearch.WordTrace]
  refine ⟨108939879851105581181364919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145253173134807441575153225 108939879851105581181364919)
  ·
    refine ⟨163409819776658371772047379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108939879851105581181364919 163409819776658371772047379)
    ·
      refine ⟨245114729664987557658071069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163409819776658371772047379 245114729664987557658071069)
      ·
        refine ⟨91918023624370334121776651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 245114729664987557658071069 91918023624370334121776651)
        ·
          refine ⟨137877035436555501182664977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91918023624370334121776651 137877035436555501182664977)
          ·
            refine ⟨103407776577416625886998733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137877035436555501182664977 103407776577416625886998733)
            ·
              refine ⟨38777916216531234707624525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103407776577416625886998733 38777916216531234707624525)
              ·
                refine ⟨14541718581199213015359197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38777916216531234707624525 14541718581199213015359197)
                ·
                  refine ⟨5453144467949704880759699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14541718581199213015359197 5453144467949704880759699)
                  ·
                    refine ⟨8179716701924557321139549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5453144467949704880759699 8179716701924557321139549)
                    ·
                      refine ⟨3067393763221708995427331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8179716701924557321139549 3067393763221708995427331)
                      ·
                        rfl

theorem cell23_5973728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3, 3, 1, 3].length) (baseStart_5973728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5973728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5973728 prefixEnd_5973728 := by exact prefixLift 5973728
  have htrace : WordTrace (prefixWord ++ tailWord_5973728) baseStart_5973728 baseEnd_5973728 := by
    simpa [prefixWord, tailWord_5973728, baseEnd_5973728] using wordTrace_append hprefix tailTrace_5973728
  have hstable : (prefixWord ++ tailWord_5973728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5973728).length < 2 ^ (prefixWord ++ tailWord_5973728).sum := by decide
  have hdescent : baseEnd_5973728 < baseStart_5973728 := by decide
  rcases family_descends (prefixWord ++ tailWord_5973728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5973738 : List Nat := [3, 1, 3, 1, 1, 1, 3, 2, 1, 5, 2]
def baseStart_5973738 : Nat := 118140960795 + 5973738 * 2 ^ 59
def prefixEnd_5973738 : Nat := 4983230072969 + 3 ^ 40 * 5973738 * 2
def baseEnd_5973738 : Nat := 3067398898028253956302285

theorem tailTrace_5973738 : CollatzResearch.WordTrace tailWord_5973738 prefixEnd_5973738 3067398898028253956302285 := by
  unfold tailWord_5973738
  simp only [CollatzResearch.WordTrace]
  refine ⟨54470031108043733517648467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145253416288116622713729245 54470031108043733517648467)
  ·
    refine ⟨81705046662065600276472701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54470031108043733517648467 81705046662065600276472701)
    ·
      refine ⟨30639392498274600103677263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81705046662065600276472701 30639392498274600103677263)
      ·
        refine ⟨45959088747411900155515895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30639392498274600103677263 45959088747411900155515895)
        ·
          refine ⟨68938633121117850233273843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45959088747411900155515895 68938633121117850233273843)
          ·
            refine ⟨103407949681676775349910765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68938633121117850233273843 103407949681676775349910765)
            ·
              refine ⟨38777981130628790756216537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103407949681676775349910765 38777981130628790756216537)
              ·
                refine ⟨29083485847971593067162403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38777981130628790756216537 29083485847971593067162403)
                ·
                  refine ⟨43625228771957389600743605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29083485847971593067162403 43625228771957389600743605)
                  ·
                    refine ⟨4089865197371005275069713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43625228771957389600743605 4089865197371005275069713)
                    ·
                      refine ⟨3067398898028253956302285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4089865197371005275069713 3067398898028253956302285)
                      ·
                        rfl

theorem cell23_5973738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 1, 5, 2].length) (baseStart_5973738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5973738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5973738 prefixEnd_5973738 := by exact prefixLift 5973738
  have htrace : WordTrace (prefixWord ++ tailWord_5973738) baseStart_5973738 baseEnd_5973738 := by
    simpa [prefixWord, tailWord_5973738, baseEnd_5973738] using wordTrace_append hprefix tailTrace_5973738
  have hstable : (prefixWord ++ tailWord_5973738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5973738).length < 2 ^ (prefixWord ++ tailWord_5973738).sum := by decide
  have hdescent : baseEnd_5973738 < baseStart_5973738 := by decide
  rcases family_descends (prefixWord ++ tailWord_5973738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5973751 : List Nat := [1, 1, 3, 1, 1, 1, 4, 3, 3, 1, 4]
def baseStart_5973751 : Nat := 118140960795 + 5973751 * 2 ^ 59
def prefixEnd_5973751 : Nat := 4983230072969 + 3 ^ 40 * 5973751 * 2
def baseEnd_5973751 : Nat := 3067405573276762405439725

theorem tailTrace_5973751 : CollatzResearch.WordTrace tailWord_5973751 prefixEnd_5973751 3067405573276762405439725 := by
  unfold tailWord_5973751
  simp only [CollatzResearch.WordTrace]
  refine ⟨217880598581127837290817107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145253732387418558193878071 217880598581127837290817107)
  ·
    refine ⟨326820897871691755936225661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217880598581127837290817107 326820897871691755936225661)
    ·
      refine ⟨122557836701884408476084623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 326820897871691755936225661 122557836701884408476084623)
      ·
        refine ⟨183836755052826612714126935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122557836701884408476084623 183836755052826612714126935)
        ·
          refine ⟨275755132579239919071190403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183836755052826612714126935 275755132579239919071190403)
          ·
            refine ⟨413632698868859878606785605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275755132579239919071190403 413632698868859878606785605)
            ·
              refine ⟨77556131037911227238772301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 413632698868859878606785605 77556131037911227238772301)
              ·
                refine ⟨29083549139216710214539613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77556131037911227238772301 29083549139216710214539613)
                ·
                  refine ⟨10906330927206266330452355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29083549139216710214539613 10906330927206266330452355)
                  ·
                    refine ⟨16359496390809399495678533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10906330927206266330452355 16359496390809399495678533)
                    ·
                      refine ⟨3067405573276762405439725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16359496390809399495678533 3067405573276762405439725)
                      ·
                        rfl

theorem cell23_5973751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 3, 1, 4].length) (baseStart_5973751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5973751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5973751 prefixEnd_5973751 := by exact prefixLift 5973751
  have htrace : WordTrace (prefixWord ++ tailWord_5973751) baseStart_5973751 baseEnd_5973751 := by
    simpa [prefixWord, tailWord_5973751, baseEnd_5973751] using wordTrace_append hprefix tailTrace_5973751
  have hstable : (prefixWord ++ tailWord_5973751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5973751).length < 2 ^ (prefixWord ++ tailWord_5973751).sum := by decide
  have hdescent : baseEnd_5973751 < baseStart_5973751 := by decide
  rcases family_descends (prefixWord ++ tailWord_5973751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5973761 : List Nat := [1, 2, 4, 1, 1, 1, 2, 4, 1, 6]
def baseStart_5973761 : Nat := 118140960795 + 5973761 * 2 ^ 59
def prefixEnd_5973761 : Nat := 4983230072969 + 3 ^ 40 * 5973761 * 2
def baseEnd_5973761 : Nat := 1022470236027769122104893

theorem tailTrace_5973761 : CollatzResearch.WordTrace tailWord_5973761 prefixEnd_5973761 1022470236027769122104893 := by
  unfold tailWord_5973761
  simp only [CollatzResearch.WordTrace]
  refine ⟨217880963311091608998681137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145253975540727739332454091 217880963311091608998681137)
  ·
    refine ⟨163410722483318706749010853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217880963311091608998681137 163410722483318706749010853)
    ·
      refine ⟨30639510465622257515439535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163410722483318706749010853 30639510465622257515439535)
      ·
        refine ⟨45959265698433386273159303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30639510465622257515439535 45959265698433386273159303)
        ·
          refine ⟨68938898547650079409738955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45959265698433386273159303 68938898547650079409738955)
          ·
            refine ⟨103408347821475119114608433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68938898547650079409738955 103408347821475119114608433)
            ·
              refine ⟨77556260866106339335956325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103408347821475119114608433 77556260866106339335956325)
              ·
                refine ⟨14541798912394938625491811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77556260866106339335956325 14541798912394938625491811)
                ·
                  refine ⟨21812698368592407938237717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14541798912394938625491811 21812698368592407938237717)
                  ·
                    refine ⟨1022470236027769122104893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21812698368592407938237717 1022470236027769122104893)
                    ·
                      rfl

theorem cell23_5973761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_5973761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5973761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5973761 prefixEnd_5973761 := by exact prefixLift 5973761
  have htrace : WordTrace (prefixWord ++ tailWord_5973761) baseStart_5973761 baseEnd_5973761 := by
    simpa [prefixWord, tailWord_5973761, baseEnd_5973761] using wordTrace_append hprefix tailTrace_5973761
  have hstable : (prefixWord ++ tailWord_5973761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5973761).length < 2 ^ (prefixWord ++ tailWord_5973761).sum := by decide
  have hdescent : baseEnd_5973761 < baseStart_5973761 := by decide
  rcases family_descends (prefixWord ++ tailWord_5973761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5973768 : List Nat := [2, 1, 3, 2, 2, 1, 1, 5, 1, 1, 4]
def baseStart_5973768 : Nat := 118140960795 + 5973768 * 2 ^ 59
def prefixEnd_5973768 : Nat := 4983230072969 + 3 ^ 40 * 5973768 * 2
def baseEnd_5973768 : Nat := 3067414302447888838927147

theorem tailTrace_5973768 : CollatzResearch.WordTrace tailWord_5973768 prefixEnd_5973768 3067414302447888838927147 := by
  unfold tailWord_5973768
  simp only [CollatzResearch.WordTrace]
  refine ⟨108940609311033124597092979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145254145748044166129457305 108940609311033124597092979)
  ·
    refine ⟨163410913966549686895639469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108940609311033124597092979 163410913966549686895639469)
    ·
      refine ⟨61279092737456132585864801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163410913966549686895639469 61279092737456132585864801)
      ·
        refine ⟨45959319553092099439398601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61279092737456132585864801 45959319553092099439398601)
        ·
          refine ⟨34469489664819074579548951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45959319553092099439398601 34469489664819074579548951)
          ·
            refine ⟨51704234497228611869323427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34469489664819074579548951 51704234497228611869323427)
            ·
              refine ⟨77556351745842917803985141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51704234497228611869323427 77556351745842917803985141)
              ·
                refine ⟨7270907976172773544123607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77556351745842917803985141 7270907976172773544123607)
                ·
                  refine ⟨10906361964259160316185411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7270907976172773544123607 10906361964259160316185411)
                  ·
                    refine ⟨16359542946388740474278117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10906361964259160316185411 16359542946388740474278117)
                    ·
                      refine ⟨3067414302447888838927147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16359542946388740474278117 3067414302447888838927147)
                      ·
                        rfl

theorem cell23_5973768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 5, 1, 1, 4].length) (baseStart_5973768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5973768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5973768 prefixEnd_5973768 := by exact prefixLift 5973768
  have htrace : WordTrace (prefixWord ++ tailWord_5973768) baseStart_5973768 baseEnd_5973768 := by
    simpa [prefixWord, tailWord_5973768, baseEnd_5973768] using wordTrace_append hprefix tailTrace_5973768
  have hstable : (prefixWord ++ tailWord_5973768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5973768).length < 2 ^ (prefixWord ++ tailWord_5973768).sum := by decide
  have hdescent : baseEnd_5973768 < baseStart_5973768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5973768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5973771 : List Nat := [1, 1, 1, 1, 5, 1, 3, 3, 1, 1, 5]
def baseStart_5973771 : Nat := 118140960795 + 5973771 * 2 ^ 59
def prefixEnd_5973771 : Nat := 4983230072969 + 3 ^ 40 * 5973771 * 2
def baseEnd_5973771 : Nat := 3067415842889852327189633

theorem tailTrace_5973771 : CollatzResearch.WordTrace tailWord_5973771 prefixEnd_5973771 3067415842889852327189633 := by
  unfold tailWord_5973771
  simp only [CollatzResearch.WordTrace]
  refine ⟨217881328041055380706545167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145254218694036920471030111 217881328041055380706545167)
  ·
    refine ⟨326821992061583071059817751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217881328041055380706545167 326821992061583071059817751)
    ·
      refine ⟨490232988092374606589726627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326821992061583071059817751 490232988092374606589726627)
      ·
        refine ⟨735349482138561909884589941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 490232988092374606589726627 735349482138561909884589941)
        ·
          refine ⟨68939013950490179051680307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 735349482138561909884589941 68939013950490179051680307)
          ·
            refine ⟨103408520925735268577520461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68939013950490179051680307 103408520925735268577520461)
            ·
              refine ⟨38778195347150725716570173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103408520925735268577520461 38778195347150725716570173)
              ·
                refine ⟨14541823255181522143713815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38778195347150725716570173 14541823255181522143713815)
                ·
                  refine ⟨21812734882772283215570723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14541823255181522143713815 21812734882772283215570723)
                  ·
                    refine ⟨32719102324158424823356085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21812734882772283215570723 32719102324158424823356085)
                    ·
                      refine ⟨3067415842889852327189633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32719102324158424823356085 3067415842889852327189633)
                      ·
                        rfl

theorem cell23_5973771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3, 1, 1, 5].length) (baseStart_5973771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5973771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5973771 prefixEnd_5973771 := by exact prefixLift 5973771
  have htrace : WordTrace (prefixWord ++ tailWord_5973771) baseStart_5973771 baseEnd_5973771 := by
    simpa [prefixWord, tailWord_5973771, baseEnd_5973771] using wordTrace_append hprefix tailTrace_5973771
  have hstable : (prefixWord ++ tailWord_5973771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5973771).length < 2 ^ (prefixWord ++ tailWord_5973771).sum := by decide
  have hdescent : baseEnd_5973771 < baseStart_5973771 := by decide
  rcases family_descends (prefixWord ++ tailWord_5973771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5973773 : List Nat := [1, 7, 2, 1, 2, 1, 1, 1, 3, 4]
def baseStart_5973773 : Nat := 118140960795 + 5973773 * 2 ^ 59
def prefixEnd_5973773 : Nat := 4983230072969 + 3 ^ 40 * 5973773 * 2
def baseEnd_5973773 : Nat := 1022472289950387106454875

theorem tailTrace_5973773 : CollatzResearch.WordTrace tailWord_5973773 prefixEnd_5973773 1022472289950387106454875 := by
  unfold tailWord_5973773
  simp only [CollatzResearch.WordTrace]
  refine ⟨217881400987048135048117973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145254267324698756698745315 217881400987048135048117973)
  ·
    refine ⟨5106595335633940665190265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 217881400987048135048117973 5106595335633940665190265)
    ·
      refine ⟨3829946501725455498892699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5106595335633940665190265 3829946501725455498892699)
      ·
        refine ⟨5744919752588183248339049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3829946501725455498892699 5744919752588183248339049)
        ·
          refine ⟨4308689814441137436254287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5744919752588183248339049 4308689814441137436254287)
          ·
            refine ⟨6463034721661706154381431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4308689814441137436254287 6463034721661706154381431)
            ·
              refine ⟨9694552082492559231572147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6463034721661706154381431 9694552082492559231572147)
              ·
                refine ⟨14541828123738838847358221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9694552082492559231572147 14541828123738838847358221)
                ·
                  refine ⟨5453185546402064567759333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14541828123738838847358221 5453185546402064567759333)
                  ·
                    refine ⟨1022472289950387106454875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5453185546402064567759333 1022472289950387106454875)
                    ·
                      rfl

theorem cell23_5973773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_5973773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5973773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5973773 prefixEnd_5973773 := by exact prefixLift 5973773
  have htrace : WordTrace (prefixWord ++ tailWord_5973773) baseStart_5973773 baseEnd_5973773 := by
    simpa [prefixWord, tailWord_5973773, baseEnd_5973773] using wordTrace_append hprefix tailTrace_5973773
  have hstable : (prefixWord ++ tailWord_5973773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5973773).length < 2 ^ (prefixWord ++ tailWord_5973773).sum := by decide
  have hdescent : baseEnd_5973773 < baseStart_5973773 := by decide
  rcases family_descends (prefixWord ++ tailWord_5973773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5973781 : List Nat := [1, 3, 2, 1, 2, 3, 1, 2, 1, 1, 6]
def baseStart_5973781 : Nat := 118140960795 + 5973781 * 2 ^ 59
def prefixEnd_5973781 : Nat := 4983230072969 + 3 ^ 40 * 5973781 * 2
def baseEnd_5973781 : Nat := 3067420977696397288064587

theorem tailTrace_5973781 : CollatzResearch.WordTrace tailWord_5973781 prefixEnd_5973781 3067420977696397288064587 := by
  unfold tailWord_5973781
  simp only [CollatzResearch.WordTrace]
  refine ⟨217881692771019152414409197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145254461847346101609606131 217881692771019152414409197)
  ·
    refine ⟨81705634789132182155403449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217881692771019152414409197 81705634789132182155403449)
    ·
      refine ⟨61279226091849136616552587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81705634789132182155403449 61279226091849136616552587)
      ·
        refine ⟨91918839137773704924828881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61279226091849136616552587 91918839137773704924828881)
        ·
          refine ⟨68939129353330278693621661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91918839137773704924828881 68939129353330278693621661)
          ·
            refine ⟨25852173507498854510108123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68939129353330278693621661 25852173507498854510108123)
            ·
              refine ⟨38778260261248281765162185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25852173507498854510108123 38778260261248281765162185)
              ·
                refine ⟨29083695195936211323871639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38778260261248281765162185 29083695195936211323871639)
                ·
                  refine ⟨43625542793904316985807459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29083695195936211323871639 43625542793904316985807459)
                  ·
                    refine ⟨65438314190856475478711189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43625542793904316985807459 65438314190856475478711189)
                    ·
                      refine ⟨3067420977696397288064587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65438314190856475478711189 3067420977696397288064587)
                      ·
                        rfl

theorem cell23_5973781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_5973781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5973781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5973781 prefixEnd_5973781 := by exact prefixLift 5973781
  have htrace : WordTrace (prefixWord ++ tailWord_5973781) baseStart_5973781 baseEnd_5973781 := by
    simpa [prefixWord, tailWord_5973781, baseEnd_5973781] using wordTrace_append hprefix tailTrace_5973781
  have hstable : (prefixWord ++ tailWord_5973781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5973781).length < 2 ^ (prefixWord ++ tailWord_5973781).sum := by decide
  have hdescent : baseEnd_5973781 < baseStart_5973781 := by decide
  rcases family_descends (prefixWord ++ tailWord_5973781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5973788 : List Nat := [2, 2, 3, 1, 1, 2, 2, 2, 3, 2, 3]
def baseStart_5973788 : Nat := 118140960795 + 5973788 * 2 ^ 59
def prefixEnd_5973788 : Nat := 4983230072969 + 3 ^ 40 * 5973788 * 2
def baseEnd_5973788 : Nat := 3067424572060978760677055

theorem tailTrace_5973788 : CollatzResearch.WordTrace tailWord_5973788 prefixEnd_5973788 3067424572060978760677055 := by
  unfold tailWord_5973788
  simp only [CollatzResearch.WordTrace]
  refine ⟨108940974040996896304957009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145254632054662528406609345 108940974040996896304957009)
  ·
    refine ⟨81705730530747672228717757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108940974040996896304957009 81705730530747672228717757)
    ·
      refine ⟨30639648949030377085769159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81705730530747672228717757 30639648949030377085769159)
      ·
        refine ⟨45959473423545565628653739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30639648949030377085769159 45959473423545565628653739)
        ·
          refine ⟨68939210135318348442980609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45959473423545565628653739 68939210135318348442980609)
          ·
            refine ⟨51704407601488761332235457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68939210135318348442980609 51704407601488761332235457)
            ·
              refine ⟨38778305701116570999176593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51704407601488761332235457 38778305701116570999176593)
              ·
                refine ⟨29083729275837428249382445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38778305701116570999176593 29083729275837428249382445)
                ·
                  refine ⟨10906398478439035593518417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29083729275837428249382445 10906398478439035593518417)
                  ·
                    refine ⟨8179798858829276695138813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10906398478439035593518417 8179798858829276695138813)
                    ·
                      refine ⟨3067424572060978760677055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8179798858829276695138813 3067424572060978760677055)
                      ·
                        rfl

theorem cell23_5973788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_5973788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5973788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5973788 prefixEnd_5973788 := by exact prefixLift 5973788
  have htrace : WordTrace (prefixWord ++ tailWord_5973788) baseStart_5973788 baseEnd_5973788 := by
    simpa [prefixWord, tailWord_5973788, baseEnd_5973788] using wordTrace_append hprefix tailTrace_5973788
  have hstable : (prefixWord ++ tailWord_5973788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5973788).length < 2 ^ (prefixWord ++ tailWord_5973788).sum := by decide
  have hdescent : baseEnd_5973788 < baseStart_5973788 := by decide
  rcases family_descends (prefixWord ++ tailWord_5973788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5973791 : List Nat := [1, 1, 2, 4, 2, 1, 4, 8]
def baseStart_5973791 : Nat := 118140960795 + 5973791 * 2 ^ 59
def prefixEnd_5973791 : Nat := 4983230072969 + 3 ^ 40 * 5973791 * 2
def baseEnd_5973791 : Nat := 113608374537146009219983

theorem tailTrace_5973791 : CollatzResearch.WordTrace tailWord_5973791 prefixEnd_5973791 113608374537146009219983 := by
  unfold tailWord_5973791
  simp only [CollatzResearch.WordTrace]
  refine ⟨217882057500982924122273227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145254705000655282748182151 217882057500982924122273227)
  ·
    refine ⟨326823086251474386183409841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217882057500982924122273227 326823086251474386183409841)
    ·
      refine ⟨245117314688605789637557381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326823086251474386183409841 245117314688605789637557381)
      ·
        refine ⟨45959496504113585557042009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 245117314688605789637557381 45959496504113585557042009)
        ·
          refine ⟨34469622378085189167781507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45959496504113585557042009 34469622378085189167781507)
          ·
            refine ⟨51704433567127783751672261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34469622378085189167781507 51704433567127783751672261)
            ·
              refine ⟨9694581293836459453438549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51704433567127783751672261 9694581293836459453438549)
              ·
                refine ⟨113608374537146009219983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9694581293836459453438549 113608374537146009219983)
                ·
                  rfl

theorem cell23_5973791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 8].length) (baseStart_5973791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5973791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5973791 prefixEnd_5973791 := by exact prefixLift 5973791
  have htrace : WordTrace (prefixWord ++ tailWord_5973791) baseStart_5973791 baseEnd_5973791 := by
    simpa [prefixWord, tailWord_5973791, baseEnd_5973791] using wordTrace_append hprefix tailTrace_5973791
  have hstable : (prefixWord ++ tailWord_5973791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5973791).length < 2 ^ (prefixWord ++ tailWord_5973791).sum := by decide
  have hdescent : baseEnd_5973791 < baseStart_5973791 := by decide
  rcases family_descends (prefixWord ++ tailWord_5973791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5973795 : List Nat := [1, 1, 1, 4, 2, 1, 6, 1, 2, 4]
def baseStart_5973795 : Nat := 118140960795 + 5973795 * 2 ^ 59
def prefixEnd_5973795 : Nat := 4983230072969 + 3 ^ 40 * 5973795 * 2
def baseEnd_5973795 : Nat := 1022476055475186744429841

theorem tailTrace_5973795 : CollatzResearch.WordTrace tailWord_5973795 prefixEnd_5973795 1022476055475186744429841 := by
  unfold tailWord_5973795
  simp only [CollatzResearch.WordTrace]
  refine ⟨217882203392968432805418839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145254802261978955203612559 217882203392968432805418839)
  ·
    refine ⟨326823305089452649208128259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217882203392968432805418839 326823305089452649208128259)
    ·
      refine ⟨490234957634178973812192389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326823305089452649208128259 490234957634178973812192389)
      ·
        refine ⟨91919054556408557589786073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 490234957634178973812192389 91919054556408557589786073)
        ·
          refine ⟨68939290917306418192339555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91919054556408557589786073 68939290917306418192339555)
          ·
            refine ⟨103408936375959627288509333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68939290917306418192339555 103408936375959627288509333)
            ·
              refine ⟨4847293892623107529148875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 103408936375959627288509333 4847293892623107529148875)
              ·
                refine ⟨7270940838934661293723313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4847293892623107529148875 7270940838934661293723313)
                ·
                  refine ⟨5453205629200995970292485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7270940838934661293723313 5453205629200995970292485)
                  ·
                    refine ⟨1022476055475186744429841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5453205629200995970292485 1022476055475186744429841)
                    ·
                      rfl

theorem cell23_5973795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6, 1, 2, 4].length) (baseStart_5973795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5973795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5973795 prefixEnd_5973795 := by exact prefixLift 5973795
  have htrace : WordTrace (prefixWord ++ tailWord_5973795) baseStart_5973795 baseEnd_5973795 := by
    simpa [prefixWord, tailWord_5973795, baseEnd_5973795] using wordTrace_append hprefix tailTrace_5973795
  have hstable : (prefixWord ++ tailWord_5973795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5973795).length < 2 ^ (prefixWord ++ tailWord_5973795).sum := by decide
  have hdescent : baseEnd_5973795 < baseStart_5973795 := by decide
  rcases family_descends (prefixWord ++ tailWord_5973795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5973818 : List Nat := [3, 1, 1, 1, 5, 1, 1, 1, 3, 3, 3]
def baseStart_5973818 : Nat := 118140960795 + 5973818 * 2 ^ 59
def prefixEnd_5973818 : Nat := 4983230072969 + 3 ^ 40 * 5973818 * 2
def baseEnd_5973818 : Nat := 3067439976480613643301917

theorem tailTrace_5973818 : CollatzResearch.WordTrace tailWord_5973818 prefixEnd_5973818 3067439976480613643301917 := by
  unfold tailWord_5973818
  simp only [CollatzResearch.WordTrace]
  refine ⟨54470760567971276933376527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145255361514590071822337405 54470760567971276933376527)
  ·
    refine ⟨81706140851956915400064791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54470760567971276933376527 81706140851956915400064791)
    ·
      refine ⟨122559211277935373100097187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81706140851956915400064791 122559211277935373100097187)
      ·
        refine ⟨183838816916903059650145781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122559211277935373100097187 183838816916903059650145781)
        ·
          refine ⟨17234889085959661842201167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 183838816916903059650145781 17234889085959661842201167)
          ·
            refine ⟨25852333628939492763301751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17234889085959661842201167 25852333628939492763301751)
            ·
              refine ⟨38778500443409239144952627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25852333628939492763301751 38778500443409239144952627)
              ·
                refine ⟨58167750665113858717428941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38778500443409239144952627 58167750665113858717428941)
                ·
                  refine ⟨21812906499417697019035853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58167750665113858717428941 21812906499417697019035853)
                  ·
                    refine ⟨8179839937281636382138445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21812906499417697019035853 8179839937281636382138445)
                    ·
                      refine ⟨3067439976480613643301917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8179839937281636382138445 3067439976480613643301917)
                      ·
                        rfl

theorem cell23_5973818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 3, 3, 3].length) (baseStart_5973818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5973818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5973818 prefixEnd_5973818 := by exact prefixLift 5973818
  have htrace : WordTrace (prefixWord ++ tailWord_5973818) baseStart_5973818 baseEnd_5973818 := by
    simpa [prefixWord, tailWord_5973818, baseEnd_5973818] using wordTrace_append hprefix tailTrace_5973818
  have hstable : (prefixWord ++ tailWord_5973818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5973818).length < 2 ^ (prefixWord ++ tailWord_5973818).sum := by decide
  have hdescent : baseEnd_5973818 < baseStart_5973818 := by decide
  rcases family_descends (prefixWord ++ tailWord_5973818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5973831 : List Nat := [1, 1, 4, 1, 2, 1, 2, 2, 2, 2, 5]
def baseStart_5973831 : Nat := 118140960795 + 5973831 * 2 ^ 59
def prefixEnd_5973831 : Nat := 4983230072969 + 3 ^ 40 * 5973831 * 2
def baseEnd_5973831 : Nat := 3067446651729122092439357

theorem tailTrace_5973831 : CollatzResearch.WordTrace tailWord_5973831 prefixEnd_5973831 3067446651729122092439357 := by
  unfold tailWord_5973831
  simp only [CollatzResearch.WordTrace]
  refine ⟨217883516420838010953729347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145255677613892007302486231 217883516420838010953729347)
  ·
    refine ⟨326825274631257016430594021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217883516420838010953729347 326825274631257016430594021)
    ·
      refine ⟨61279738993360690580736379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 326825274631257016430594021 61279738993360690580736379)
      ·
        refine ⟨91919608490041035871104569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61279738993360690580736379 91919608490041035871104569)
        ·
          refine ⟨68939706367530776903328427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91919608490041035871104569 68939706367530776903328427)
          ·
            refine ⟨103409559551296165354992641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68939706367530776903328427 103409559551296165354992641)
            ·
              refine ⟨77557169663472124016244481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103409559551296165354992641 77557169663472124016244481)
              ·
                refine ⟨58167877247604093012183361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77557169663472124016244481 58167877247604093012183361)
                ·
                  refine ⟨43625907935703069759137521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58167877247604093012183361 43625907935703069759137521)
                  ·
                    refine ⟨32719430951777302319353141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43625907935703069759137521 32719430951777302319353141)
                    ·
                      refine ⟨3067446651729122092439357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32719430951777302319353141 3067446651729122092439357)
                      ·
                        rfl

theorem cell23_5973831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_5973831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5973831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5973831 prefixEnd_5973831 := by exact prefixLift 5973831
  have htrace : WordTrace (prefixWord ++ tailWord_5973831) baseStart_5973831 baseEnd_5973831 := by
    simpa [prefixWord, tailWord_5973831, baseEnd_5973831] using wordTrace_append hprefix tailTrace_5973831
  have hstable : (prefixWord ++ tailWord_5973831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5973831).length < 2 ^ (prefixWord ++ tailWord_5973831).sum := by decide
  have hdescent : baseEnd_5973831 < baseStart_5973831 := by decide
  rcases family_descends (prefixWord ++ tailWord_5973831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5973845 : List Nat := [1, 3, 2, 2, 2, 2, 1, 2, 3, 3, 2]
def baseStart_5973845 : Nat := 118140960795 + 5973845 * 2 ^ 59
def prefixEnd_5973845 : Nat := 4983230072969 + 3 ^ 40 * 5973845 * 2
def baseEnd_5973845 : Nat := 3067453840458285037664293

theorem tailTrace_5973845 : CollatzResearch.WordTrace tailWord_5973845 prefixEnd_5973845 3067453840458285037664293 := by
  unfold tailWord_5973845
  simp only [CollatzResearch.WordTrace]
  refine ⟨217884027042787291344738989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145256018028524860896492659 217884027042787291344738989)
  ·
    refine ⟨81706510141045234254277121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217884027042787291344738989 81706510141045234254277121)
    ·
      refine ⟨61279882605783925690707841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81706510141045234254277121 61279882605783925690707841)
      ·
        refine ⟨45959911954337944268030881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61279882605783925690707841 45959911954337944268030881)
        ·
          refine ⟨34469933965753458201023161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45959911954337944268030881 34469933965753458201023161)
          ·
            refine ⟨25852450474315093650767371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34469933965753458201023161 25852450474315093650767371)
            ·
              refine ⟨38778675711472640476151057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25852450474315093650767371 38778675711472640476151057)
              ·
                refine ⟨29084006783604480357113293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38778675711472640476151057 29084006783604480357113293)
                ·
                  refine ⟨10906502543851680133917485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29084006783604480357113293 10906502543851680133917485)
                  ·
                    refine ⟨4089938453944380050219057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10906502543851680133917485 4089938453944380050219057)
                    ·
                      refine ⟨3067453840458285037664293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4089938453944380050219057 3067453840458285037664293)
                      ·
                        rfl

theorem cell23_5973845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 3, 3, 2].length) (baseStart_5973845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5973845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5973845 prefixEnd_5973845 := by exact prefixLift 5973845
  have htrace : WordTrace (prefixWord ++ tailWord_5973845) baseStart_5973845 baseEnd_5973845 := by
    simpa [prefixWord, tailWord_5973845, baseEnd_5973845] using wordTrace_append hprefix tailTrace_5973845
  have hstable : (prefixWord ++ tailWord_5973845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5973845).length < 2 ^ (prefixWord ++ tailWord_5973845).sum := by decide
  have hdescent : baseEnd_5973845 < baseStart_5973845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5973845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5973852 : List Nat := [2, 2, 4, 2, 2, 1, 2, 1, 1, 3, 3]
def baseStart_5973852 : Nat := 118140960795 + 5973852 * 2 ^ 59
def prefixEnd_5973852 : Nat := 4983230072969 + 3 ^ 40 * 5973852 * 2
def baseEnd_5973852 : Nat := 3067457434822866510276761

theorem tailTrace_5973852 : CollatzResearch.WordTrace tailWord_5973852 prefixEnd_5973852 3067457434822866510276761 := by
  unfold tailWord_5973852
  simp only [CollatzResearch.WordTrace]
  refine ⟨108942141176880965770121905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145256188235841287693495873 108942141176880965770121905)
  ·
    refine ⟨81706605882660724327591429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108942141176880965770121905 81706605882660724327591429)
    ·
      refine ⟨15319988602998885811423393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81706605882660724327591429 15319988602998885811423393)
      ·
        refine ⟨11489991452249164358567545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15319988602998885811423393 11489991452249164358567545)
        ·
          refine ⟨8617493589186873268925659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11489991452249164358567545 8617493589186873268925659)
          ·
            refine ⟨12926240383780309903388489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8617493589186873268925659 12926240383780309903388489)
            ·
              refine ⟨9694680287835232427541367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12926240383780309903388489 9694680287835232427541367)
              ·
                refine ⟨14542020431752848641312051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9694680287835232427541367 14542020431752848641312051)
                ·
                  refine ⟨21813030647629272961968077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14542020431752848641312051 21813030647629272961968077)
                  ·
                    refine ⟨8179886492860977360738029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21813030647629272961968077 8179886492860977360738029)
                    ·
                      refine ⟨3067457434822866510276761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8179886492860977360738029 3067457434822866510276761)
                      ·
                        rfl

theorem cell23_5973852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_5973852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5973852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5973852 prefixEnd_5973852 := by exact prefixLift 5973852
  have htrace : WordTrace (prefixWord ++ tailWord_5973852) baseStart_5973852 baseEnd_5973852 := by
    simpa [prefixWord, tailWord_5973852, baseEnd_5973852] using wordTrace_append hprefix tailTrace_5973852
  have hstable : (prefixWord ++ tailWord_5973852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5973852).length < 2 ^ (prefixWord ++ tailWord_5973852).sum := by decide
  have hdescent : baseEnd_5973852 < baseStart_5973852 := by decide
  rcases family_descends (prefixWord ++ tailWord_5973852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5973875 : List Nat := [1, 1, 1, 2, 2, 1, 3, 4, 4, 2, 2]
def baseStart_5973875 : Nat := 118140960795 + 5973875 * 2 ^ 59
def prefixEnd_5973875 : Nat := 4983230072969 + 3 ^ 40 * 5973875 * 2
def baseEnd_5973875 : Nat := 3067469244877919920289155

theorem tailTrace_5973875 : CollatzResearch.WordTrace tailWord_5973875 prefixEnd_5973875 3067469244877919920289155 := by
  unfold tailWord_5973875
  simp only [CollatzResearch.WordTrace]
  refine ⟨217885121232678606468331079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145256747488452404312220719 217885121232678606468331079)
  ·
    refine ⟨326827681849017909702496619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217885121232678606468331079 326827681849017909702496619)
    ·
      refine ⟨490241522773526864553744929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326827681849017909702496619 490241522773526864553744929)
      ·
        refine ⟨367681142080145148415308697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 490241522773526864553744929 367681142080145148415308697)
        ·
          refine ⟨275760856560108861311481523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 367681142080145148415308697 275760856560108861311481523)
          ·
            refine ⟨413641284840163291967222285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275760856560108861311481523 413641284840163291967222285)
            ·
              refine ⟨155115481815061234487708357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 413641284840163291967222285 155115481815061234487708357)
              ·
                refine ⟨29084152840323981466445317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 155115481815061234487708357 29084152840323981466445317)
                ·
                  refine ⟨5453278657560746524958497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29084152840323981466445317 5453278657560746524958497)
                  ·
                    refine ⟨4089958993170559893718873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5453278657560746524958497 4089958993170559893718873)
                    ·
                      refine ⟨3067469244877919920289155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4089958993170559893718873 3067469244877919920289155)
                      ·
                        rfl

theorem cell23_5973875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 4, 2, 2].length) (baseStart_5973875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5973875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5973875 prefixEnd_5973875 := by exact prefixLift 5973875
  have htrace : WordTrace (prefixWord ++ tailWord_5973875) baseStart_5973875 baseEnd_5973875 := by
    simpa [prefixWord, tailWord_5973875, baseEnd_5973875] using wordTrace_append hprefix tailTrace_5973875
  have hstable : (prefixWord ++ tailWord_5973875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5973875).length < 2 ^ (prefixWord ++ tailWord_5973875).sum := by decide
  have hdescent : baseEnd_5973875 < baseStart_5973875 := by decide
  rcases family_descends (prefixWord ++ tailWord_5973875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5973881 : List Nat := [1, 2, 1, 3, 2, 2, 1, 2, 9]
def baseStart_5973881 : Nat := 118140960795 + 5973881 * 2 ^ 59
def prefixEnd_5973881 : Nat := 4983230072969 + 3 ^ 40 * 5973881 * 2
def baseEnd_5973881 : Nat := 340830258417982988534903

theorem tailTrace_5973881 : CollatzResearch.WordTrace tailWord_5973881 prefixEnd_5973881 340830258417982988534903 := by
  unfold tailWord_5973881
  simp only [CollatzResearch.WordTrace]
  refine ⟨217885340070656869493049497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145256893380437912995366331 217885340070656869493049497)
  ·
    refine ⟨163414005052992652119787123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217885340070656869493049497 163414005052992652119787123)
    ·
      refine ⟨245121007579488978179680685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163414005052992652119787123 245121007579488978179680685)
      ·
        refine ⟨91920377842308366817380257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 245121007579488978179680685 91920377842308366817380257)
        ·
          refine ⟨68940283381731275113035193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91920377842308366817380257 68940283381731275113035193)
          ·
            refine ⟨51705212536298456334776395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68940283381731275113035193 51705212536298456334776395)
            ·
              refine ⟨77557818804447684502164593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51705212536298456334776395 77557818804447684502164593)
              ·
                refine ⟨58168364103335763376623445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77557818804447684502164593 58168364103335763376623445)
                ·
                  refine ⟨340830258417982988534903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 58168364103335763376623445 340830258417982988534903)
                  ·
                    rfl

theorem cell23_5973881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 9].length) (baseStart_5973881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5973881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5973881 prefixEnd_5973881 := by exact prefixLift 5973881
  have htrace : WordTrace (prefixWord ++ tailWord_5973881) baseStart_5973881 baseEnd_5973881 := by
    simpa [prefixWord, tailWord_5973881, baseEnd_5973881] using wordTrace_append hprefix tailTrace_5973881
  have hstable : (prefixWord ++ tailWord_5973881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5973881).length < 2 ^ (prefixWord ++ tailWord_5973881).sum := by decide
  have hdescent : baseEnd_5973881 < baseStart_5973881 := by decide
  rcases family_descends (prefixWord ++ tailWord_5973881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5973886 : List Nat := [4, 2, 3, 1, 1, 3, 1, 2, 2, 1, 3]
def baseStart_5973886 : Nat := 118140960795 + 5973886 * 2 ^ 59
def prefixEnd_5973886 : Nat := 4983230072969 + 3 ^ 40 * 5973886 * 2
def baseEnd_5973886 : Nat := 3067474893165119377251605

theorem tailTrace_5973886 : CollatzResearch.WordTrace tailWord_5973886 prefixEnd_5973886 3067474893165119377251605 := by
  unfold tailWord_5973886
  simp only [CollatzResearch.WordTrace]
  refine ⟨27235690304454844418372689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145257014957092503564654341 27235690304454844418372689)
  ·
    refine ⟨20426767728341133313779517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27235690304454844418372689 20426767728341133313779517)
    ·
      refine ⟨7660037898127924992667319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20426767728341133313779517 7660037898127924992667319)
      ·
        refine ⟨11490056847191887489000979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7660037898127924992667319 11490056847191887489000979)
        ·
          refine ⟨17235085270787831233501469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11490056847191887489000979 17235085270787831233501469)
          ·
            refine ⟨6463156976545436712563051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17235085270787831233501469 6463156976545436712563051)
            ·
              refine ⟨9694735464818155068844577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6463156976545436712563051 9694735464818155068844577)
              ·
                refine ⟨7271051598613616301633433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9694735464818155068844577 7271051598613616301633433)
                ·
                  refine ⟨5453288698960212226225075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7271051598613616301633433 5453288698960212226225075)
                  ·
                    refine ⟨8179933048440318339337613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5453288698960212226225075 8179933048440318339337613)
                    ·
                      refine ⟨3067474893165119377251605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8179933048440318339337613 3067474893165119377251605)
                      ·
                        rfl

theorem cell23_5973886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_5973886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5973886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5973886 prefixEnd_5973886 := by exact prefixLift 5973886
  have htrace : WordTrace (prefixWord ++ tailWord_5973886) baseStart_5973886 baseEnd_5973886 := by
    simpa [prefixWord, tailWord_5973886, baseEnd_5973886] using wordTrace_append hprefix tailTrace_5973886
  have hstable : (prefixWord ++ tailWord_5973886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5973886).length < 2 ^ (prefixWord ++ tailWord_5973886).sum := by decide
  have hdescent : baseEnd_5973886 < baseStart_5973886 := by decide
  rcases family_descends (prefixWord ++ tailWord_5973886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5973909 : List Nat := [1, 3, 2, 1, 1, 3, 5, 1, 2, 2, 2]
def baseStart_5973909 : Nat := 118140960795 + 5973909 * 2 ^ 59
def prefixEnd_5973909 : Nat := 4983230072969 + 3 ^ 40 * 5973909 * 2
def baseEnd_5973909 : Nat := 3067486703220172787263999

theorem tailTrace_5973909 : CollatzResearch.WordTrace tailWord_5973909 prefixEnd_5973909 3067486703220172787263999 := by
  unfold tailWord_5973909
  simp only [CollatzResearch.WordTrace]
  refine ⟨217886361314555430275068781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145257574209703620183379187 217886361314555430275068781)
  ·
    refine ⟨81707385492958286353150793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217886361314555430275068781 81707385492958286353150793)
    ·
      refine ⟨61280539119718714764863095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81707385492958286353150793 61280539119718714764863095)
      ·
        refine ⟨91920808679578072147294643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61280539119718714764863095 91920808679578072147294643)
        ·
          refine ⟨137881213019367108220941965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91920808679578072147294643 137881213019367108220941965)
          ·
            refine ⟨51705454882262665582853237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137881213019367108220941965 51705454882262665582853237)
            ·
              refine ⟨4847386395212124898392491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51705454882262665582853237 4847386395212124898392491)
              ·
                refine ⟨7271079592818187347588737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4847386395212124898392491 7271079592818187347588737)
                ·
                  refine ⟨5453309694613640510691553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7271079592818187347588737 5453309694613640510691553)
                  ·
                    refine ⟨4089982270960230383018665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5453309694613640510691553 4089982270960230383018665)
                    ·
                      refine ⟨3067486703220172787263999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4089982270960230383018665 3067486703220172787263999)
                      ·
                        rfl

theorem cell23_5973909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5, 1, 2, 2, 2].length) (baseStart_5973909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5973909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5973909 prefixEnd_5973909 := by exact prefixLift 5973909
  have htrace : WordTrace (prefixWord ++ tailWord_5973909) baseStart_5973909 baseEnd_5973909 := by
    simpa [prefixWord, tailWord_5973909, baseEnd_5973909] using wordTrace_append hprefix tailTrace_5973909
  have hstable : (prefixWord ++ tailWord_5973909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5973909).length < 2 ^ (prefixWord ++ tailWord_5973909).sum := by decide
  have hdescent : baseEnd_5973909 < baseStart_5973909 := by decide
  rcases family_descends (prefixWord ++ tailWord_5973909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5973968 : List Nat := [2, 1, 1, 1, 1, 2, 4, 1, 3, 4, 3]
def baseStart_5973968 : Nat := 118140960795 + 5973968 * 2 ^ 59
def prefixEnd_5973968 : Nat := 4983230072969 + 3 ^ 40 * 5973968 * 2
def baseEnd_5973968 : Nat := 3067516998578788056426227

theorem tailTrace_5973968 : CollatzResearch.WordTrace tailWord_5973968 prefixEnd_5973968 3067516998578788056426227 := by
  unfold tailWord_5973968
  simp only [CollatzResearch.WordTrace]
  refine ⟨108944256610670841675733279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145259008814227788900977705 108944256610670841675733279)
  ·
    refine ⟨163416384916006262513599919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108944256610670841675733279 163416384916006262513599919)
    ·
      refine ⟨245124577374009393770399879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163416384916006262513599919 245124577374009393770399879)
      ·
        refine ⟨367686866061014090655599819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245124577374009393770399879 367686866061014090655599819)
        ·
          refine ⟨551530299091521135983399729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367686866061014090655599819 551530299091521135983399729)
          ·
            refine ⟨413647724318640851987549797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 551530299091521135983399729 413647724318640851987549797)
            ·
              refine ⟨77558948309745159747665587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 413647724318640851987549797 77558948309745159747665587)
              ·
                refine ⟨116338422464617739621498381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77558948309745159747665587 116338422464617739621498381)
                ·
                  refine ⟨43626908424231652358061893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 116338422464617739621498381 43626908424231652358061893)
                  ·
                    refine ⟨8180045329543434817136605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43626908424231652358061893 8180045329543434817136605)
                    ·
                      refine ⟨3067516998578788056426227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8180045329543434817136605 3067516998578788056426227)
                      ·
                        rfl

theorem cell23_5973968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4, 3].length) (baseStart_5973968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5973968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5973968 prefixEnd_5973968 := by exact prefixLift 5973968
  have htrace : WordTrace (prefixWord ++ tailWord_5973968) baseStart_5973968 baseEnd_5973968 := by
    simpa [prefixWord, tailWord_5973968, baseEnd_5973968] using wordTrace_append hprefix tailTrace_5973968
  have hstable : (prefixWord ++ tailWord_5973968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5973968).length < 2 ^ (prefixWord ++ tailWord_5973968).sum := by decide
  have hdescent : baseEnd_5973968 < baseStart_5973968 := by decide
  rcases family_descends (prefixWord ++ tailWord_5973968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5973985 : List Nat := [1, 2, 3, 1, 2, 1, 3, 3, 2, 2, 3]
def baseStart_5973985 : Nat := 118140960795 + 5973985 * 2 ^ 59
def prefixEnd_5973985 : Nat := 4983230072969 + 3 ^ 40 * 5973985 * 2
def baseEnd_5973985 : Nat := 3067525727749914489913649

theorem tailTrace_5973985 : CollatzResearch.WordTrace tailWord_5973985 prefixEnd_5973985 3067525727749914489913649 := by
  unfold tailWord_5973985
  simp only [CollatzResearch.WordTrace]
  refine ⟨217889133262280095254835409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145259422174853396836556939 217889133262280095254835409)
  ·
    refine ⟨163416849946710071441126557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217889133262280095254835409 163416849946710071441126557)
    ·
      refine ⟨61281318730016276790422459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163416849946710071441126557 61281318730016276790422459)
      ·
        refine ⟨91921978095024415185633689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61281318730016276790422459 91921978095024415185633689)
        ·
          refine ⟨68941483571268311389225267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91921978095024415185633689 68941483571268311389225267)
          ·
            refine ⟨103412225356902467083837901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68941483571268311389225267 103412225356902467083837901)
            ·
              refine ⟨38779584508838425156439213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103412225356902467083837901 38779584508838425156439213)
              ·
                refine ⟨14542344190814409433664705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38779584508838425156439213 14542344190814409433664705)
                ·
                  refine ⟨10906758143110807075248529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14542344190814409433664705 10906758143110807075248529)
                  ·
                    refine ⟨8180068607333105306436397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10906758143110807075248529 8180068607333105306436397)
                    ·
                      refine ⟨3067525727749914489913649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8180068607333105306436397 3067525727749914489913649)
                      ·
                        rfl

theorem cell23_5973985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3, 2, 2, 3].length) (baseStart_5973985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5973985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5973985 prefixEnd_5973985 := by exact prefixLift 5973985
  have htrace : WordTrace (prefixWord ++ tailWord_5973985) baseStart_5973985 baseEnd_5973985 := by
    simpa [prefixWord, tailWord_5973985, baseEnd_5973985] using wordTrace_append hprefix tailTrace_5973985
  have hstable : (prefixWord ++ tailWord_5973985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5973985).length < 2 ^ (prefixWord ++ tailWord_5973985).sum := by decide
  have hdescent : baseEnd_5973985 < baseStart_5973985 := by decide
  rcases family_descends (prefixWord ++ tailWord_5973985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5973992 : List Nat := [2, 1, 4, 1, 1, 1, 1, 7, 1, 4]
def baseStart_5973992 : Nat := 118140960795 + 5973992 * 2 ^ 59
def prefixEnd_5973992 : Nat := 4983230072969 + 3 ^ 40 * 5973992 * 2
def baseEnd_5973992 : Nat := 1022509774038165320842039

theorem tailTrace_5973992 : CollatzResearch.WordTrace tailWord_5973992 prefixEnd_5973992 1022509774038165320842039 := by
  unfold tailWord_5973992
  simp only [CollatzResearch.WordTrace]
  refine ⟨108944694286627367725170115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145259592382169823633560153 108944694286627367725170115)
  ·
    refine ⟨163417041429941051587755173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108944694286627367725170115 163417041429941051587755173)
    ·
      refine ⟨30640695268113947172704095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163417041429941051587755173 30640695268113947172704095)
      ·
        refine ⟨45961042902170920759056143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30640695268113947172704095 45961042902170920759056143)
        ·
          refine ⟨68941564353256381138584215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45961042902170920759056143 68941564353256381138584215)
          ·
            refine ⟨103412346529884571707876323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68941564353256381138584215 103412346529884571707876323)
            ·
              refine ⟨155118519794826857561814485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103412346529884571707876323 155118519794826857561814485)
              ·
                refine ⟨3635590307691254474105027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 155118519794826857561814485 3635590307691254474105027)
                ·
                  refine ⟨5453385461536881711157541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3635590307691254474105027 5453385461536881711157541)
                  ·
                    refine ⟨1022509774038165320842039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5453385461536881711157541 1022509774038165320842039)
                    ·
                      rfl

theorem cell23_5973992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 7, 1, 4].length) (baseStart_5973992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5973992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5973992 prefixEnd_5973992 := by exact prefixLift 5973992
  have htrace : WordTrace (prefixWord ++ tailWord_5973992) baseStart_5973992 baseEnd_5973992 := by
    simpa [prefixWord, tailWord_5973992, baseEnd_5973992] using wordTrace_append hprefix tailTrace_5973992
  have hstable : (prefixWord ++ tailWord_5973992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5973992).length < 2 ^ (prefixWord ++ tailWord_5973992).sum := by decide
  have hdescent : baseEnd_5973992 < baseStart_5973992 := by decide
  rcases family_descends (prefixWord ++ tailWord_5973992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5974009 : List Nat := [1, 2, 1, 3, 1, 4, 4, 2, 1, 4]
def baseStart_5974009 : Nat := 118140960795 + 5974009 * 2 ^ 59
def prefixEnd_5974009 : Nat := 4983230072969 + 3 ^ 40 * 5974009 * 2
def baseEnd_5974009 : Nat := 1022512683761874132004513

theorem tailTrace_5974009 : CollatzResearch.WordTrace tailWord_5974009 prefixEnd_5974009 1022512683761874132004513 := by
  unfold tailWord_5974009
  simp only [CollatzResearch.WordTrace]
  refine ⟨217890008614193147353709081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145260005742795431569139387 217890008614193147353709081)
  ·
    refine ⟨163417506460644860515281811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217890008614193147353709081 163417506460644860515281811)
    ·
      refine ⟨245126259690967290772922717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163417506460644860515281811 245126259690967290772922717)
      ·
        refine ⟨91922347384112734039846019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 245126259690967290772922717 91922347384112734039846019)
        ·
          refine ⟨137883521076169101059769029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91922347384112734039846019 137883521076169101059769029)
          ·
            refine ⟨25853160201781706448706693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 137883521076169101059769029 25853160201781706448706693)
            ·
              refine ⟨4847467537834069959132505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25853160201781706448706693 4847467537834069959132505)
              ·
                refine ⟨3635600653375552469349379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4847467537834069959132505 3635600653375552469349379)
                ·
                  refine ⟨5453400980063328704024069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3635600653375552469349379 5453400980063328704024069)
                  ·
                    refine ⟨1022512683761874132004513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5453400980063328704024069 1022512683761874132004513)
                    ·
                      rfl

theorem cell23_5974009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4, 2, 1, 4].length) (baseStart_5974009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974009 prefixEnd_5974009 := by exact prefixLift 5974009
  have htrace : WordTrace (prefixWord ++ tailWord_5974009) baseStart_5974009 baseEnd_5974009 := by
    simpa [prefixWord, tailWord_5974009, baseEnd_5974009] using wordTrace_append hprefix tailTrace_5974009
  have hstable : (prefixWord ++ tailWord_5974009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974009).length < 2 ^ (prefixWord ++ tailWord_5974009).sum := by decide
  have hdescent : baseEnd_5974009 < baseStart_5974009 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5974015 : List Nat := [1, 1, 2, 2, 1, 2, 1, 2, 7, 1, 3]
def baseStart_5974015 : Nat := 118140960795 + 5974015 * 2 ^ 59
def prefixEnd_5974015 : Nat := 4983230072969 + 3 ^ 40 * 5974015 * 2
def baseEnd_5974015 : Nat := 3067541132169549372538511

theorem tailTrace_5974015 : CollatzResearch.WordTrace tailWord_5974015 prefixEnd_5974015 3067541132169549372538511 := by
  unfold tailWord_5974015
  simp only [CollatzResearch.WordTrace]
  refine ⟨217890227452171410378427499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145260151634780940252284999 217890227452171410378427499)
  ·
    refine ⟨326835341178257115567641249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217890227452171410378427499 326835341178257115567641249)
    ·
      refine ⟨245126505883692836675730937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326835341178257115567641249 245126505883692836675730937)
      ·
        refine ⟨183844879412769627506798203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245126505883692836675730937 183844879412769627506798203)
        ·
          refine ⟨275767319119154441260197305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183844879412769627506798203 275767319119154441260197305)
          ·
            refine ⟨206825489339365830945147979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 275767319119154441260197305 206825489339365830945147979)
            ·
              refine ⟨310238234009048746417721969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206825489339365830945147979 310238234009048746417721969)
              ·
                refine ⟨232678675506786559813291477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 310238234009048746417721969 232678675506786559813291477)
                ·
                  refine ⟨5453406457190309995624019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 232678675506786559813291477 5453406457190309995624019)
                  ·
                    refine ⟨8180109685785464993436029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5453406457190309995624019 8180109685785464993436029)
                    ·
                      refine ⟨3067541132169549372538511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8180109685785464993436029 3067541132169549372538511)
                      ·
                        rfl

theorem cell23_5974015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 7, 1, 3].length) (baseStart_5974015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974015 prefixEnd_5974015 := by exact prefixLift 5974015
  have htrace : WordTrace (prefixWord ++ tailWord_5974015) baseStart_5974015 baseEnd_5974015 := by
    simpa [prefixWord, tailWord_5974015, baseEnd_5974015] using wordTrace_append hprefix tailTrace_5974015
  have hstable : (prefixWord ++ tailWord_5974015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974015).length < 2 ^ (prefixWord ++ tailWord_5974015).sum := by decide
  have hdescent : baseEnd_5974015 < baseStart_5974015 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5974028 : List Nat := [2, 2, 1, 2, 3, 1, 1, 1, 2, 1, 7]
def baseStart_5974028 : Nat := 118140960795 + 5974028 * 2 ^ 59
def prefixEnd_5974028 : Nat := 4983230072969 + 3 ^ 40 * 5974028 * 2
def baseEnd_5974028 : Nat := 3067547807418057821675951

theorem tailTrace_5974028 : CollatzResearch.WordTrace tailWord_5974028 prefixEnd_5974028 3067547807418057821675951 := by
  unfold tailWord_5974028
  simp only [CollatzResearch.WordTrace]
  refine ⟨108945350800562156799325369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145260467734082875732433825 108945350800562156799325369)
  ·
    refine ⟨81709013100421617599494027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108945350800562156799325369 81709013100421617599494027)
    ·
      refine ⟨122563519650632426399241041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81709013100421617599494027 122563519650632426399241041)
      ·
        refine ⟨91922639737974319799430781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122563519650632426399241041 91922639737974319799430781)
        ·
          refine ⟨34470989901740369924786543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91922639737974319799430781 34470989901740369924786543)
          ·
            refine ⟨51706484852610554887179815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34470989901740369924786543 51706484852610554887179815)
            ·
              refine ⟨77559727278915832330769723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51706484852610554887179815 77559727278915832330769723)
              ·
                refine ⟨116339590918373748496154585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77559727278915832330769723 116339590918373748496154585)
                ·
                  refine ⟨87254693188780311372115939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116339590918373748496154585 87254693188780311372115939)
                  ·
                    refine ⟨130882039783170467058173909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 87254693188780311372115939 130882039783170467058173909)
                    ·
                      refine ⟨3067547807418057821675951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 130882039783170467058173909 3067547807418057821675951)
                      ·
                        rfl

theorem cell23_5974028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_5974028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974028 prefixEnd_5974028 := by exact prefixLift 5974028
  have htrace : WordTrace (prefixWord ++ tailWord_5974028) baseStart_5974028 baseEnd_5974028 := by
    simpa [prefixWord, tailWord_5974028, baseEnd_5974028] using wordTrace_append hprefix tailTrace_5974028
  have hstable : (prefixWord ++ tailWord_5974028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974028).length < 2 ^ (prefixWord ++ tailWord_5974028).sum := by decide
  have hdescent : baseEnd_5974028 < baseStart_5974028 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5974042 : List Nat := [3, 1, 1, 3, 1, 4, 1, 1, 1, 5, 2]
def baseStart_5974042 : Nat := 118140960795 + 5974042 * 2 ^ 59
def prefixEnd_5974042 : Nat := 4983230072969 + 3 ^ 40 * 5974042 * 2
def baseEnd_5974042 : Nat := 3067554996147220766900887

theorem tailTrace_5974042 : CollatzResearch.WordTrace tailWord_5974042 prefixEnd_5974042 3067554996147220766900887 := by
  unfold tailWord_5974042
  simp only [CollatzResearch.WordTrace]
  refine ⟨54472803055768398497415095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145260808148715729326440253 54472803055768398497415095)
  ·
    refine ⟨81709204583652597746122643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54472803055768398497415095 81709204583652597746122643)
    ·
      refine ⟨122563806875478896619183965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81709204583652597746122643 122563806875478896619183965)
      ·
        refine ⟨45961427578304586232193987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122563806875478896619183965 45961427578304586232193987)
        ·
          refine ⟨68942141367456879348290981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45961427578304586232193987 68942141367456879348290981)
          ·
            refine ⟨12926651506398164877804559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68942141367456879348290981 12926651506398164877804559)
            ·
              refine ⟨19389977259597247316706839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12926651506398164877804559 19389977259597247316706839)
              ·
                refine ⟨29084965889395870975060259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19389977259597247316706839 29084965889395870975060259)
                ·
                  refine ⟨43627448834093806462590389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29084965889395870975060259 43627448834093806462590389)
                  ·
                    refine ⟨4090073328196294355867849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43627448834093806462590389 4090073328196294355867849)
                    ·
                      refine ⟨3067554996147220766900887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4090073328196294355867849 3067554996147220766900887)
                      ·
                        rfl

theorem cell23_5974042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 1, 5, 2].length) (baseStart_5974042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974042 prefixEnd_5974042 := by exact prefixLift 5974042
  have htrace : WordTrace (prefixWord ++ tailWord_5974042) baseStart_5974042 baseEnd_5974042 := by
    simpa [prefixWord, tailWord_5974042, baseEnd_5974042] using wordTrace_append hprefix tailTrace_5974042
  have hstable : (prefixWord ++ tailWord_5974042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974042).length < 2 ^ (prefixWord ++ tailWord_5974042).sum := by decide
  have hdescent : baseEnd_5974042 < baseStart_5974042 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5974056 : List Nat := [2, 1, 5, 3, 2, 1, 1, 2, 6]
def baseStart_5974056 : Nat := 118140960795 + 5974056 * 2 ^ 59
def prefixEnd_5974056 : Nat := 4983230072969 + 3 ^ 40 * 5974056 * 2
def baseEnd_5974056 : Nat := 340840242764042634680647

theorem tailTrace_5974056 : CollatzResearch.WordTrace tailWord_5974056 prefixEnd_5974056 340840242764042634680647 := by
  unfold tailWord_5974056
  simp only [CollatzResearch.WordTrace]
  refine ⟨108945861422511437190335011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145261148563348582920446681 108945861422511437190335011)
  ·
    refine ⟨163418792133767155785502517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108945861422511437190335011 163418792133767155785502517)
    ·
      refine ⟨15320511762540670854890861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 163418792133767155785502517 15320511762540670854890861)
      ·
        refine ⟨5745191910952751570584073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15320511762540670854890861 5745191910952751570584073)
        ·
          refine ⟨4308893933214563677938055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5745191910952751570584073 4308893933214563677938055)
          ·
            refine ⟨6463340899821845516907083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4308893933214563677938055 6463340899821845516907083)
            ·
              refine ⟨9695011349732768275360625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6463340899821845516907083 9695011349732768275360625)
              ·
                refine ⟨7271258512299576206520469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9695011349732768275360625 7271258512299576206520469)
                ·
                  refine ⟨340840242764042634680647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7271258512299576206520469 340840242764042634680647)
                  ·
                    rfl

theorem cell23_5974056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 2, 6].length) (baseStart_5974056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974056 prefixEnd_5974056 := by exact prefixLift 5974056
  have htrace : WordTrace (prefixWord ++ tailWord_5974056) baseStart_5974056 baseEnd_5974056 := by
    simpa [prefixWord, tailWord_5974056, baseEnd_5974056] using wordTrace_append hprefix tailTrace_5974056
  have hstable : (prefixWord ++ tailWord_5974056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974056).length < 2 ^ (prefixWord ++ tailWord_5974056).sum := by decide
  have hdescent : baseEnd_5974056 < baseStart_5974056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5974092 : List Nat := [2, 2, 1, 3, 1, 1, 3, 4, 1, 2, 3]
def baseStart_5974092 : Nat := 118140960795 + 5974092 * 2 ^ 59
def prefixEnd_5974092 : Nat := 4983230072969 + 3 ^ 40 * 5974092 * 2
def baseEnd_5974092 : Nat := 3067580670179945571275657

theorem tailTrace_5974092 : CollatzResearch.WordTrace tailWord_5974092 prefixEnd_5974092 3067580670179945571275657 := by
  unfold tailWord_5974092
  simp only [CollatzResearch.WordTrace]
  refine ⟨108946517936446226264490265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145262023915261635019320353 108946517936446226264490265)
  ·
    refine ⟨81709888452334669698367699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108946517936446226264490265 81709888452334669698367699)
    ·
      refine ⟨122564832678502004547551549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81709888452334669698367699 122564832678502004547551549)
      ·
        refine ⟨45961812254438251705331831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122564832678502004547551549 45961812254438251705331831)
        ·
          refine ⟨68942718381657377557997747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45961812254438251705331831 68942718381657377557997747)
          ·
            refine ⟨103414077572486066336996621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68942718381657377557997747 103414077572486066336996621)
            ·
              refine ⟨38780279089682274876373733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103414077572486066336996621 38780279089682274876373733)
              ·
                refine ⟨7271302329315426539320075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38780279089682274876373733 7271302329315426539320075)
                ·
                  refine ⟨10906953493973139808980113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7271302329315426539320075 10906953493973139808980113)
                  ·
                    refine ⟨8180215120479854856735085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10906953493973139808980113 8180215120479854856735085)
                    ·
                      refine ⟨3067580670179945571275657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8180215120479854856735085 3067580670179945571275657)
                      ·
                        rfl

theorem cell23_5974092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 4, 1, 2, 3].length) (baseStart_5974092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974092 prefixEnd_5974092 := by exact prefixLift 5974092
  have htrace : WordTrace (prefixWord ++ tailWord_5974092) baseStart_5974092 baseEnd_5974092 := by
    simpa [prefixWord, tailWord_5974092, baseEnd_5974092] using wordTrace_append hprefix tailTrace_5974092
  have hstable : (prefixWord ++ tailWord_5974092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974092).length < 2 ^ (prefixWord ++ tailWord_5974092).sum := by decide
  have hdescent : baseEnd_5974092 < baseStart_5974092 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5974105 : List Nat := [1, 2, 1, 2, 2, 1, 4, 1, 3, 3, 3]
def baseStart_5974105 : Nat := 118140960795 + 5974105 * 2 ^ 59
def prefixEnd_5974105 : Nat := 4983230072969 + 3 ^ 40 * 5974105 * 2
def baseEnd_5974105 : Nat := 3067587345428454020413097

theorem tailTrace_5974105 : CollatzResearch.WordTrace tailWord_5974105 prefixEnd_5974105 3067587345428454020413097 := by
  unfold tailWord_5974105
  simp only [CollatzResearch.WordTrace]
  refine ⟨217893510021845355749203769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145262340014563570499469179 217893510021845355749203769)
  ·
    refine ⟨163420132516384016811902827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217893510021845355749203769 163420132516384016811902827)
    ·
      refine ⟨245130198774576025217854241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163420132516384016811902827 245130198774576025217854241)
      ·
        refine ⟨183847649080932018913390681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245130198774576025217854241 183847649080932018913390681)
        ·
          refine ⟨137885736810699014185043011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183847649080932018913390681 137885736810699014185043011)
          ·
            refine ⟨206828605216048521277564517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137885736810699014185043011 206828605216048521277564517)
            ·
              refine ⟨38780363478009097739543347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 206828605216048521277564517 38780363478009097739543347)
              ·
                refine ⟨58170545217013646609315021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38780363478009097739543347 58170545217013646609315021)
                ·
                  refine ⟨21813954456380117478493133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58170545217013646609315021 21813954456380117478493133)
                  ·
                    refine ⟨8180232921142544054434925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21813954456380117478493133 8180232921142544054434925)
                    ·
                      refine ⟨3067587345428454020413097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8180232921142544054434925 3067587345428454020413097)
                      ·
                        rfl

theorem cell23_5974105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 3, 3, 3].length) (baseStart_5974105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974105 prefixEnd_5974105 := by exact prefixLift 5974105
  have htrace : WordTrace (prefixWord ++ tailWord_5974105) baseStart_5974105 baseEnd_5974105 := by
    simpa [prefixWord, tailWord_5974105, baseEnd_5974105] using wordTrace_append hprefix tailTrace_5974105
  have hstable : (prefixWord ++ tailWord_5974105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974105).length < 2 ^ (prefixWord ++ tailWord_5974105).sum := by decide
  have hdescent : baseEnd_5974105 < baseStart_5974105 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5974109 : List Nat := [1, 4, 4, 1, 1, 2, 2, 1, 1, 1, 5]
def baseStart_5974109 : Nat := 118140960795 + 5974109 * 2 ^ 59
def prefixEnd_5974109 : Nat := 4983230072969 + 3 ^ 40 * 5974109 * 2
def baseEnd_5974109 : Nat := 3067589399351072004763079

theorem tailTrace_5974109 : CollatzResearch.WordTrace tailWord_5974109 prefixEnd_5974109 3067589399351072004763079 := by
  unfold tailWord_5974109
  simp only [CollatzResearch.WordTrace]
  refine ⟨217893655913830864432349381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145262437275887242954899587 217893655913830864432349381)
  ·
    refine ⟨40855060483843287081065509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 217893655913830864432349381 40855060483843287081065509)
    ·
      refine ⟨7660323840720616327699783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40855060483843287081065509 7660323840720616327699783)
      ·
        refine ⟨11490485761080924491549675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7660323840720616327699783 11490485761080924491549675)
        ·
          refine ⟨17235728641621386737324513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11490485761080924491549675 17235728641621386737324513)
          ·
            refine ⟨12926796481216040052993385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17235728641621386737324513 12926796481216040052993385)
            ·
              refine ⟨9695097360912030039745039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12926796481216040052993385 9695097360912030039745039)
              ·
                refine ⟨14542646041368045059617559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9695097360912030039745039 14542646041368045059617559)
                ·
                  refine ⟨21813969062052067589426339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14542646041368045059617559 21813969062052067589426339)
                  ·
                    refine ⟨32720953593078101384139509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21813969062052067589426339 32720953593078101384139509)
                    ·
                      refine ⟨3067589399351072004763079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32720953593078101384139509 3067589399351072004763079)
                      ·
                        rfl

theorem cell23_5974109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_5974109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974109 prefixEnd_5974109 := by exact prefixLift 5974109
  have htrace : WordTrace (prefixWord ++ tailWord_5974109) baseStart_5974109 baseEnd_5974109 := by
    simpa [prefixWord, tailWord_5974109, baseEnd_5974109] using wordTrace_append hprefix tailTrace_5974109
  have hstable : (prefixWord ++ tailWord_5974109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974109).length < 2 ^ (prefixWord ++ tailWord_5974109).sum := by decide
  have hdescent : baseEnd_5974109 < baseStart_5974109 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5974125 : List Nat := [1, 5, 1, 1, 2, 1, 2, 1, 2, 7]
def baseStart_5974125 : Nat := 118140960795 + 5974125 * 2 ^ 59
def prefixEnd_5974125 : Nat := 4983230072969 + 3 ^ 40 * 5974125 * 2
def baseEnd_5974125 : Nat := 1022532538347181314054335

theorem tailTrace_5974125 : CollatzResearch.WordTrace tailWord_5974125 prefixEnd_5974125 1022532538347181314054335 := by
  unfold tailWord_5974125
  simp only [CollatzResearch.WordTrace]
  refine ⟨217894239481772899164931829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145262826321181932776621219 217894239481772899164931829)
  ·
    refine ⟨20427584951416209296712359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 217894239481772899164931829 20427584951416209296712359)
    ·
      refine ⟨30641377427124313945068539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20427584951416209296712359 30641377427124313945068539)
      ·
        refine ⟨45962066140686470917602809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30641377427124313945068539 45962066140686470917602809)
        ·
          refine ⟨34471549605514853188202107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45962066140686470917602809 34471549605514853188202107)
          ·
            refine ⟨51707324408272279782303161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34471549605514853188202107 51707324408272279782303161)
            ·
              refine ⟨38780493306204209836727371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51707324408272279782303161 38780493306204209836727371)
              ·
                refine ⟨58170739959306314755091057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38780493306204209836727371 58170739959306314755091057)
                ·
                  refine ⟨43628054969479736066318293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58170739959306314755091057 43628054969479736066318293)
                  ·
                    refine ⟨1022532538347181314054335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43628054969479736066318293 1022532538347181314054335)
                    ·
                      rfl

theorem cell23_5974125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_5974125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974125 prefixEnd_5974125 := by exact prefixLift 5974125
  have htrace : WordTrace (prefixWord ++ tailWord_5974125) baseStart_5974125 baseEnd_5974125 := by
    simpa [prefixWord, tailWord_5974125, baseEnd_5974125] using wordTrace_append hprefix tailTrace_5974125
  have hstable : (prefixWord ++ tailWord_5974125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974125).length < 2 ^ (prefixWord ++ tailWord_5974125).sum := by decide
  have hdescent : baseEnd_5974125 < baseStart_5974125 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5974149 : List Nat := [1, 3, 1, 1, 5, 2, 1, 1, 3, 3, 2]
def baseStart_5974149 : Nat := 118140960795 + 5974149 * 2 ^ 59
def prefixEnd_5974149 : Nat := 4983230072969 + 3 ^ 40 * 5974149 * 2
def baseEnd_5974149 : Nat := 3067609938577251848262895

theorem tailTrace_5974149 : CollatzResearch.WordTrace tailWord_5974149 prefixEnd_5974149 3067609938577251848262895 := by
  unfold tailWord_5974149
  simp only [CollatzResearch.WordTrace]
  refine ⟨217895114833685951263805501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145263409889123967509203667 217895114833685951263805501)
  ·
    refine ⟨81710668062632231723927063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217895114833685951263805501 81710668062632231723927063)
    ·
      refine ⟨122566002093948347585890595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81710668062632231723927063 122566002093948347585890595)
      ·
        refine ⟨183849003140922521378835893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122566002093948347585890595 183849003140922521378835893)
        ·
          refine ⟨17235844044461486379265865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 183849003140922521378835893 17235844044461486379265865)
          ·
            refine ⟨12926883033346114784449399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17235844044461486379265865 12926883033346114784449399)
            ·
              refine ⟨19390324550019172176674099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12926883033346114784449399 19390324550019172176674099)
              ·
                refine ⟨29085486825028758265011149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19390324550019172176674099 29085486825028758265011149)
                ·
                  refine ⟨10907057559385784349379181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29085486825028758265011149 10907057559385784349379181)
                  ·
                    refine ⟨4090146584769669131017193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10907057559385784349379181 4090146584769669131017193)
                    ·
                      refine ⟨3067609938577251848262895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4090146584769669131017193 3067609938577251848262895)
                      ·
                        rfl

theorem cell23_5974149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 3, 3, 2].length) (baseStart_5974149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974149 prefixEnd_5974149 := by exact prefixLift 5974149
  have htrace : WordTrace (prefixWord ++ tailWord_5974149) baseStart_5974149 baseEnd_5974149 := by
    simpa [prefixWord, tailWord_5974149, baseEnd_5974149] using wordTrace_append hprefix tailTrace_5974149
  have hstable : (prefixWord ++ tailWord_5974149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974149).length < 2 ^ (prefixWord ++ tailWord_5974149).sum := by decide
  have hdescent : baseEnd_5974149 < baseStart_5974149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5974165 : List Nat := [1, 3, 2, 1, 1, 1, 3, 3, 2, 1, 5]
def baseStart_5974165 : Nat := 118140960795 + 5974165 * 2 ^ 59
def prefixEnd_5974165 : Nat := 4983230072969 + 3 ^ 40 * 5974165 * 2
def baseEnd_5974165 : Nat := 3067618154267723785662821

theorem tailTrace_5974165 : CollatzResearch.WordTrace tailWord_5974165 prefixEnd_5974165 3067618154267723785662821 := by
  unfold tailWord_5974165
  simp only [CollatzResearch.WordTrace]
  refine ⟨217895698401627985996387949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145263798934418657330925299 217895698401627985996387949)
  ·
    refine ⟨81710886900610494748645481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217895698401627985996387949 81710886900610494748645481)
    ·
      refine ⟨61283165175457871061484111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81710886900610494748645481 61283165175457871061484111)
      ·
        refine ⟨91924747763186806592226167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61283165175457871061484111 91924747763186806592226167)
        ·
          refine ⟨137887121644780209888339251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91924747763186806592226167 137887121644780209888339251)
          ·
            refine ⟨206830682467170314832508877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137887121644780209888339251 206830682467170314832508877)
            ·
              refine ⟨77561505925188868062190829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 206830682467170314832508877 77561505925188868062190829)
              ·
                refine ⟨29085564721945825523321561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77561505925188868062190829 29085564721945825523321561)
                ·
                  refine ⟨21814173541459369142491171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29085564721945825523321561 21814173541459369142491171)
                  ·
                    refine ⟨32721260312189053713736757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21814173541459369142491171 32721260312189053713736757)
                    ·
                      refine ⟨3067618154267723785662821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32721260312189053713736757 3067618154267723785662821)
                      ·
                        rfl

theorem cell23_5974165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_5974165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974165 prefixEnd_5974165 := by exact prefixLift 5974165
  have htrace : WordTrace (prefixWord ++ tailWord_5974165) baseStart_5974165 baseEnd_5974165 := by
    simpa [prefixWord, tailWord_5974165, baseEnd_5974165] using wordTrace_append hprefix tailTrace_5974165
  have hstable : (prefixWord ++ tailWord_5974165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974165).length < 2 ^ (prefixWord ++ tailWord_5974165).sum := by decide
  have hdescent : baseEnd_5974165 < baseStart_5974165 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5974174 : List Nat := [4, 3, 1, 1, 4, 1, 2, 2, 1, 2, 2]
def baseStart_5974174 : Nat := 118140960795 + 5974174 * 2 ^ 59
def prefixEnd_5974174 : Nat := 4983230072969 + 3 ^ 40 * 5974174 * 2
def baseEnd_5974174 : Nat := 3067622775593614250450281

theorem tailTrace_5974174 : CollatzResearch.WordTrace tailWord_5974174 prefixEnd_5974174 3067622775593614250450281 := by
  unfold tailWord_5974174
  simp only [CollatzResearch.WordTrace]
  refine ⟨27237003332324422566683197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145264017772396920355643717 27237003332324422566683197)
  ·
    refine ⟨10213876249621658462506199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27237003332324422566683197 10213876249621658462506199)
    ·
      refine ⟨15320814374432487693759299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10213876249621658462506199 15320814374432487693759299)
      ·
        refine ⟨22981221561648731540638949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15320814374432487693759299 22981221561648731540638949)
        ·
          refine ⟨4308979042809137163869803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22981221561648731540638949 4308979042809137163869803)
          ·
            refine ⟨6463468564213705745804705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4308979042809137163869803 6463468564213705745804705)
            ·
              refine ⟨4847601423160279309353529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6463468564213705745804705 4847601423160279309353529)
              ·
                refine ⟨3635701067370209482015147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4847601423160279309353529 3635701067370209482015147)
                ·
                  refine ⟨5453551601055314223022721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3635701067370209482015147 5453551601055314223022721)
                  ·
                    refine ⟨4090163700791485667267041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5453551601055314223022721 4090163700791485667267041)
                    ·
                      refine ⟨3067622775593614250450281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4090163700791485667267041 3067622775593614250450281)
                      ·
                        rfl

theorem cell23_5974174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_5974174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974174 prefixEnd_5974174 := by exact prefixLift 5974174
  have htrace : WordTrace (prefixWord ++ tailWord_5974174) baseStart_5974174 baseEnd_5974174 := by
    simpa [prefixWord, tailWord_5974174, baseEnd_5974174] using wordTrace_append hprefix tailTrace_5974174
  have hstable : (prefixWord ++ tailWord_5974174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974174).length < 2 ^ (prefixWord ++ tailWord_5974174).sum := by decide
  have hdescent : baseEnd_5974174 < baseStart_5974174 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5974225 : List Nat := [1, 2, 2, 1, 2, 2, 2, 1, 3, 2, 5]
def baseStart_5974225 : Nat := 118140960795 + 5974225 * 2 ^ 59
def prefixEnd_5974225 : Nat := 4983230072969 + 3 ^ 40 * 5974225 * 2
def baseEnd_5974225 : Nat := 3067648963106993550912545

theorem tailTrace_5974225 : CollatzResearch.WordTrace tailWord_5974225 prefixEnd_5974225 3067648963106993550912545 := by
  unfold tailWord_5974225
  simp only [CollatzResearch.WordTrace]
  refine ⟨217897886781410616243572129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145265257854273744162381419 217897886781410616243572129)
  ·
    refine ⟨163423415086057962182679097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217897886781410616243572129 163423415086057962182679097)
    ·
      refine ⟨122567561314543471637009323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163423415086057962182679097 122567561314543471637009323)
      ·
        refine ⟨183851341971815207455513985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122567561314543471637009323 183851341971815207455513985)
        ·
          refine ⟨137888506478861405591635489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183851341971815207455513985 137888506478861405591635489)
          ·
            refine ⟨103416379859146054193726617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137888506478861405591635489 103416379859146054193726617)
            ·
              refine ⟨77562284894359540645294963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103416379859146054193726617 77562284894359540645294963)
              ·
                refine ⟨116343427341539310967942445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77562284894359540645294963 116343427341539310967942445)
                ·
                  refine ⟨43628785253077241612978417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 116343427341539310967942445 43628785253077241612978417)
                  ·
                    refine ⟨32721588939807931209733813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43628785253077241612978417 32721588939807931209733813)
                    ·
                      refine ⟨3067648963106993550912545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32721588939807931209733813 3067648963106993550912545)
                      ·
                        rfl

theorem cell23_5974225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 2, 5].length) (baseStart_5974225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974225 prefixEnd_5974225 := by exact prefixLift 5974225
  have htrace : WordTrace (prefixWord ++ tailWord_5974225) baseStart_5974225 baseEnd_5974225 := by
    simpa [prefixWord, tailWord_5974225, baseEnd_5974225] using wordTrace_append hprefix tailTrace_5974225
  have hstable : (prefixWord ++ tailWord_5974225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974225).length < 2 ^ (prefixWord ++ tailWord_5974225).sum := by decide
  have hdescent : baseEnd_5974225 < baseStart_5974225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5974230 : List Nat := [5, 2, 1, 2, 1, 1, 3, 2, 2, 2, 2]
def baseStart_5974230 : Nat := 118140960795 + 5974230 * 2 ^ 59
def prefixEnd_5974230 : Nat := 4983230072969 + 3 ^ 40 * 5974230 * 2
def baseEnd_5974230 : Nat := 3067651530510266031350023

theorem tailTrace_5974230 : CollatzResearch.WordTrace tailWord_5974230 prefixEnd_5974230 3067651530510266031350023 := by
  unfold tailWord_5974230
  simp only [CollatzResearch.WordTrace]
  refine ⟨13618629321649531381094009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145265379430928334731669429 13618629321649531381094009)
  ·
    refine ⟨10213971991237148535820507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13618629321649531381094009 10213971991237148535820507)
    ·
      refine ⟨15320957986855722803730761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10213971991237148535820507 15320957986855722803730761)
      ·
        refine ⟨11490718490141792102798071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15320957986855722803730761 11490718490141792102798071)
        ·
          refine ⟨17236077735212688154197107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11490718490141792102798071 17236077735212688154197107)
          ·
            refine ⟨25854116602819032231295661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17236077735212688154197107 25854116602819032231295661)
            ·
              refine ⟨9695293726057137086735873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25854116602819032231295661 9695293726057137086735873)
              ·
                refine ⟨7271470294542852815051905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9695293726057137086735873 7271470294542852815051905)
                ·
                  refine ⟨5453602720907139611288929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7271470294542852815051905 5453602720907139611288929)
                  ·
                    refine ⟨4090202040680354708466697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5453602720907139611288929 4090202040680354708466697)
                    ·
                      refine ⟨3067651530510266031350023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4090202040680354708466697 3067651530510266031350023)
                      ·
                        rfl

theorem cell23_5974230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_5974230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974230 prefixEnd_5974230 := by exact prefixLift 5974230
  have htrace : WordTrace (prefixWord ++ tailWord_5974230) baseStart_5974230 baseEnd_5974230 := by
    simpa [prefixWord, tailWord_5974230, baseEnd_5974230] using wordTrace_append hprefix tailTrace_5974230
  have hstable : (prefixWord ++ tailWord_5974230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974230).length < 2 ^ (prefixWord ++ tailWord_5974230).sum := by decide
  have hdescent : baseEnd_5974230 < baseStart_5974230 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5974235 : List Nat := [1, 1, 1, 1, 1, 1, 1, 6, 3, 3, 4]
def baseStart_5974235 : Nat := 118140960795 + 5974235 * 2 ^ 59
def prefixEnd_5974235 : Nat := 4983230072969 + 3 ^ 40 * 5974235 * 2
def baseEnd_5974235 : Nat := 3067654097913538511787499

theorem tailTrace_5974235 : CollatzResearch.WordTrace tailWord_5974235 prefixEnd_5974235 3067654097913538511787499 := by
  unfold tailWord_5974235
  simp only [CollatzResearch.WordTrace]
  refine ⟨217898251511374387951436159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145265501007582925300957439 217898251511374387951436159)
  ·
    refine ⟨326847377267061581927154239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217898251511374387951436159 326847377267061581927154239)
    ·
      refine ⟨490271065900592372890731359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326847377267061581927154239 490271065900592372890731359)
      ·
        refine ⟨735406598850888559336097039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 490271065900592372890731359 735406598850888559336097039)
        ·
          refine ⟨1103109898276332839004145559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 735406598850888559336097039 1103109898276332839004145559)
          ·
            refine ⟨1654664847414499258506218339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1103109898276332839004145559 1654664847414499258506218339)
            ·
              refine ⟨2481997271121748887759327509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1654664847414499258506218339 2481997271121748887759327509)
              ·
                refine ⟨116343622083831979113718477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2481997271121748887759327509 116343622083831979113718477)
                ·
                  refine ⟨43628858281436992167644429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 116343622083831979113718477 43628858281436992167644429)
                  ·
                    refine ⟨16360821855538872062866661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43628858281436992167644429 16360821855538872062866661)
                    ·
                      refine ⟨3067654097913538511787499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16360821855538872062866661 3067654097913538511787499)
                      ·
                        rfl

theorem cell23_5974235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 3, 4].length) (baseStart_5974235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974235 prefixEnd_5974235 := by exact prefixLift 5974235
  have htrace : WordTrace (prefixWord ++ tailWord_5974235) baseStart_5974235 baseEnd_5974235 := by
    simpa [prefixWord, tailWord_5974235, baseEnd_5974235] using wordTrace_append hprefix tailTrace_5974235
  have hstable : (prefixWord ++ tailWord_5974235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974235).length < 2 ^ (prefixWord ++ tailWord_5974235).sum := by decide
  have hdescent : baseEnd_5974235 < baseStart_5974235 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5974236 : List Nat := [2, 2, 5, 2, 1, 1, 2, 1, 7]
def baseStart_5974236 : Nat := 118140960795 + 5974236 * 2 ^ 59
def prefixEnd_5974236 : Nat := 4983230072969 + 3 ^ 40 * 5974236 * 2
def baseEnd_5974236 : Nat := 340850512377132556430555

theorem tailTrace_5974236 : CollatzResearch.WordTrace tailWord_5974236 prefixEnd_5974236 340850512377132556430555 := by
  unfold tailWord_5974236
  simp only [CollatzResearch.WordTrace]
  refine ⟨108949143992185382561111281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145265525322913843414815041 108949143992185382561111281)
  ·
    refine ⟨81711857994139036920833461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108949143992185382561111281 81711857994139036920833461)
    ·
      refine ⟨7660486686950534711328137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81711857994139036920833461 7660486686950534711328137)
      ·
        refine ⟨5745365015212901033496103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7660486686950534711328137 5745365015212901033496103)
        ·
          refine ⟨8618047522819351550244155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5745365015212901033496103 8618047522819351550244155)
          ·
            refine ⟨12927071284229027325366233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8618047522819351550244155 12927071284229027325366233)
            ·
              refine ⟨9695303463171770494024675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12927071284229027325366233 9695303463171770494024675)
              ·
                refine ⟨14542955194757655741037013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9695303463171770494024675 14542955194757655741037013)
                ·
                  refine ⟨340850512377132556430555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14542955194757655741037013 340850512377132556430555)
                  ·
                    rfl

theorem cell23_5974236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 1, 7].length) (baseStart_5974236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974236 prefixEnd_5974236 := by exact prefixLift 5974236
  have htrace : WordTrace (prefixWord ++ tailWord_5974236) baseStart_5974236 baseEnd_5974236 := by
    simpa [prefixWord, tailWord_5974236, baseEnd_5974236] using wordTrace_append hprefix tailTrace_5974236
  have hstable : (prefixWord ++ tailWord_5974236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974236).length < 2 ^ (prefixWord ++ tailWord_5974236).sum := by decide
  have hdescent : baseEnd_5974236 < baseStart_5974236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
