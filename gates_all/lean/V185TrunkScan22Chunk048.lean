import V185TrunkScan22Chunk047

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_430174 : List Nat := [4, 4, 1, 1, 2, 1, 3, 2, 4]
def baseStart_430174 : Nat := 118140960795 + 430174 * 2 ^ 59
def prefixEnd_430174 : Nat := 4983230072969 + 3 ^ 40 * 430174 * 2
def baseEnd_430174 : Nat := 49085783792734483543705

theorem tailTrace_430174 : CollatzResearch.WordTrace tailWord_430174 prefixEnd_430174 49085783792734483543705 := by
  unfold tailWord_430174
  simp only [CollatzResearch.WordTrace]
  refine ⟨1961216842945067589404197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10459823162373693810155717 1961216842945067589404197)
  ·
    refine ⟨367728158052200173013287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1961216842945067589404197 367728158052200173013287)
    ·
      refine ⟨551592237078300259519931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367728158052200173013287 551592237078300259519931)
      ·
        refine ⟨827388355617450389279897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 551592237078300259519931 827388355617450389279897)
        ·
          refine ⟨620541266713087791959923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 827388355617450389279897 620541266713087791959923)
          ·
            refine ⟨930811900069631687939885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 620541266713087791959923 930811900069631687939885)
            ·
              refine ⟨349054462526111882977457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 930811900069631687939885 349054462526111882977457)
              ·
                refine ⟨261790846894583912233093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 349054462526111882977457 261790846894583912233093)
                ·
                  refine ⟨49085783792734483543705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 261790846894583912233093 49085783792734483543705)
                  ·
                    rfl

theorem cell22_430174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_430174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_430174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_430174 prefixEnd_430174 := by exact prefixLift 430174
  have htrace : WordTrace (prefixWord ++ tailWord_430174) baseStart_430174 baseEnd_430174 := by
    simpa [prefixWord, tailWord_430174, baseEnd_430174] using wordTrace_append hprefix tailTrace_430174
  have hstable : (prefixWord ++ tailWord_430174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430174).length < 2 ^ (prefixWord ++ tailWord_430174).sum := by decide
  have hdescent : baseEnd_430174 < baseStart_430174 := by decide
  rcases family_descends (prefixWord ++ tailWord_430174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430179 : List Nat := [1, 1, 1, 5, 1, 1, 4, 1, 7]
def baseStart_430179 : Nat := 118140960795 + 430179 * 2 ^ 59
def prefixEnd_430179 : Nat := 4983230072969 + 3 ^ 40 * 430179 * 2
def baseEnd_430179 : Nat := 49086354326795034752033

theorem tailTrace_430179 : CollatzResearch.WordTrace tailWord_430179 prefixEnd_430179 49086354326795034752033 := by
  unfold tailWord_430179
  simp only [CollatzResearch.WordTrace]
  refine ⟨15689917108542426569165591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10459944739028284379443727 15689917108542426569165591)
  ·
    refine ⟨23534875662813639853748387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15689917108542426569165591 23534875662813639853748387)
    ·
      refine ⟨35302313494220459780622581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23534875662813639853748387 35302313494220459780622581)
      ·
        refine ⟨3309591890083168104433367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35302313494220459780622581 3309591890083168104433367)
        ·
          refine ⟨4964387835124752156650051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3309591890083168104433367 4964387835124752156650051)
          ·
            refine ⟨7446581752687128234975077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4964387835124752156650051 7446581752687128234975077)
            ·
              refine ⟨1396234078628836544057827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7446581752687128234975077 1396234078628836544057827)
              ·
                refine ⟨2094351117943254816086741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1396234078628836544057827 2094351117943254816086741)
                ·
                  refine ⟨49086354326795034752033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2094351117943254816086741 49086354326795034752033)
                  ·
                    rfl

theorem cell22_430179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 7].length) (baseStart_430179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_430179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_430179 prefixEnd_430179 := by exact prefixLift 430179
  have htrace : WordTrace (prefixWord ++ tailWord_430179) baseStart_430179 baseEnd_430179 := by
    simpa [prefixWord, tailWord_430179, baseEnd_430179] using wordTrace_append hprefix tailTrace_430179
  have hstable : (prefixWord ++ tailWord_430179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430179).length < 2 ^ (prefixWord ++ tailWord_430179).sum := by decide
  have hdescent : baseEnd_430179 < baseStart_430179 := by decide
  rcases family_descends (prefixWord ++ tailWord_430179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430234 : List Nat := [3, 1, 1, 5, 2, 2, 2, 2, 1, 3]
def baseStart_430234 : Nat := 118140960795 + 430234 * 2 ^ 59
def prefixEnd_430234 : Nat := 4983230072969 + 3 ^ 40 * 430234 * 2
def baseEnd_430234 : Nat := 147277890604383294130931

theorem tailTrace_430234 : CollatzResearch.WordTrace tailWord_430234 prefixEnd_430234 147277890604383294130931 := by
  unfold tailWord_430234
  simp only [CollatzResearch.WordTrace]
  refine ⟨3922980780835792740604439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10461282082228780641611837 3922980780835792740604439)
  ·
    refine ⟨5884471171253689110906659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3922980780835792740604439 5884471171253689110906659)
    ·
      refine ⟨8826706756880533666359989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5884471171253689110906659 8826706756880533666359989)
      ·
        refine ⟨827503758457550031221249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8826706756880533666359989 827503758457550031221249)
        ·
          refine ⟨620627818843162523415937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 827503758457550031221249 620627818843162523415937)
          ·
            refine ⟨465470864132371892561953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 620627818843162523415937 465470864132371892561953)
            ·
              refine ⟨349103148099278919421465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 465470864132371892561953 349103148099278919421465)
              ·
                refine ⟨261827361074459189566099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 349103148099278919421465 261827361074459189566099)
                ·
                  refine ⟨392741041611688784349149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 261827361074459189566099 392741041611688784349149)
                  ·
                    refine ⟨147277890604383294130931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 392741041611688784349149 147277890604383294130931)
                    ·
                      rfl

theorem cell22_430234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2, 2, 1, 3].length) (baseStart_430234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_430234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_430234 prefixEnd_430234 := by exact prefixLift 430234
  have htrace : WordTrace (prefixWord ++ tailWord_430234) baseStart_430234 baseEnd_430234 := by
    simpa [prefixWord, tailWord_430234, baseEnd_430234] using wordTrace_append hprefix tailTrace_430234
  have hstable : (prefixWord ++ tailWord_430234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430234).length < 2 ^ (prefixWord ++ tailWord_430234).sum := by decide
  have hdescent : baseEnd_430234 < baseStart_430234 := by decide
  rcases family_descends (prefixWord ++ tailWord_430234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430286 : List Nat := [4, 1, 1, 1, 4, 2, 9]
def baseStart_430286 : Nat := 118140960795 + 430286 * 2 ^ 59
def prefixEnd_430286 : Nat := 4983230072969 + 3 ^ 40 * 430286 * 2
def baseEnd_430286 : Nat := 5455395972854536734473

theorem tailTrace_430286 : CollatzResearch.WordTrace tailWord_430286 prefixEnd_430286 5455395972854536734473 := by
  unfold tailWord_430286
  simp only [CollatzResearch.WordTrace]
  refine ⟨1961727464894347980413839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10462546479436522562207141 1961727464894347980413839)
  ·
    refine ⟨2942591197341521970620759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1961727464894347980413839 2942591197341521970620759)
    ·
      refine ⟨4413886796012282955931139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2942591197341521970620759 4413886796012282955931139)
      ·
        refine ⟨6620830194018424433896709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4413886796012282955931139 6620830194018424433896709)
        ·
          refine ⟨1241405661378454581355633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6620830194018424433896709 1241405661378454581355633)
          ·
            refine ⟨931054246033840936016725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1241405661378454581355633 931054246033840936016725)
            ·
              refine ⟨5455395972854536734473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 931054246033840936016725 5455395972854536734473)
              ·
                rfl

theorem cell22_430286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 9].length) (baseStart_430286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_430286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_430286 prefixEnd_430286 := by exact prefixLift 430286
  have htrace : WordTrace (prefixWord ++ tailWord_430286) baseStart_430286 baseEnd_430286 := by
    simpa [prefixWord, tailWord_430286, baseEnd_430286] using wordTrace_append hprefix tailTrace_430286
  have hstable : (prefixWord ++ tailWord_430286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430286).length < 2 ^ (prefixWord ++ tailWord_430286).sum := by decide
  have hdescent : baseEnd_430286 < baseStart_430286 := by decide
  rcases family_descends (prefixWord ++ tailWord_430286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430290 : List Nat := [3, 2, 2, 2, 1, 2, 3, 2, 2, 3]
def baseStart_430290 : Nat := 118140960795 + 430290 * 2 ^ 59
def prefixEnd_430290 : Nat := 4983230072969 + 3 ^ 40 * 430290 * 2
def baseEnd_430290 : Nat := 147297060548817814730759

theorem tailTrace_430290 : CollatzResearch.WordTrace tailWord_430290 prefixEnd_430290 147297060548817814730759 := by
  unfold tailWord_430290
  simp only [CollatzResearch.WordTrace]
  refine ⟨3923491402785073131614081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10462643740760195017637549 3923491402785073131614081)
  ·
    refine ⟨2942618552088804848710561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3923491402785073131614081 2942618552088804848710561)
    ·
      refine ⟨2206963914066603636532921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2942618552088804848710561 2206963914066603636532921)
      ·
        refine ⟨1655222935549952727399691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2206963914066603636532921 1655222935549952727399691)
        ·
          refine ⟨2482834403324929091099537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1655222935549952727399691 2482834403324929091099537)
          ·
            refine ⟨1862125802493696818324653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2482834403324929091099537 1862125802493696818324653)
            ·
              refine ⟨698297175935136306871745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1862125802493696818324653 698297175935136306871745)
              ·
                refine ⟨523722881951352230153809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 698297175935136306871745 523722881951352230153809)
                ·
                  refine ⟨392792161463514172615357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 523722881951352230153809 392792161463514172615357)
                  ·
                    refine ⟨147297060548817814730759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 392792161463514172615357 147297060548817814730759)
                    ·
                      rfl

theorem cell22_430290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_430290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_430290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_430290 prefixEnd_430290 := by exact prefixLift 430290
  have htrace : WordTrace (prefixWord ++ tailWord_430290) baseStart_430290 baseEnd_430290 := by
    simpa [prefixWord, tailWord_430290, baseEnd_430290] using wordTrace_append hprefix tailTrace_430290
  have hstable : (prefixWord ++ tailWord_430290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430290).length < 2 ^ (prefixWord ++ tailWord_430290).sum := by decide
  have hdescent : baseEnd_430290 < baseStart_430290 := by decide
  rcases family_descends (prefixWord ++ tailWord_430290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430307 : List Nat := [1, 1, 1, 8, 2, 1, 1, 1, 1, 5]
def baseStart_430307 : Nat := 118140960795 + 430307 * 2 ^ 59
def prefixEnd_430307 : Nat := 4983230072969 + 3 ^ 40 * 430307 * 2
def baseEnd_430307 : Nat := 147302879996235437055707

theorem tailTrace_430307 : CollatzResearch.WordTrace tailWord_430307 prefixEnd_430307 147302879996235437055707 := by
  unfold tailWord_430307
  simp only [CollatzResearch.WordTrace]
  refine ⟨15694585652078704429825175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10463057101385802953216783 15694585652078704429825175)
  ·
    refine ⟨23541878478118056644737763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15694585652078704429825175 23541878478118056644737763)
    ·
      refine ⟨35312817717177084967106645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23541878478118056644737763 35312817717177084967106645)
      ·
        refine ⟨413822082623168964458281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 35312817717177084967106645 413822082623168964458281)
        ·
          refine ⟨310366561967376723343711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 413822082623168964458281 310366561967376723343711)
          ·
            refine ⟨465549842951065085015567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310366561967376723343711 465549842951065085015567)
            ·
              refine ⟨698324764426597627523351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 465549842951065085015567 698324764426597627523351)
              ·
                refine ⟨1047487146639896441285027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 698324764426597627523351 1047487146639896441285027)
                ·
                  refine ⟨1571230719959844661927541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1047487146639896441285027 1571230719959844661927541)
                  ·
                    refine ⟨147302879996235437055707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1571230719959844661927541 147302879996235437055707)
                    ·
                      rfl

theorem cell22_430307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 1, 1, 5].length) (baseStart_430307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_430307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_430307 prefixEnd_430307 := by exact prefixLift 430307
  have htrace : WordTrace (prefixWord ++ tailWord_430307) baseStart_430307 baseEnd_430307 := by
    simpa [prefixWord, tailWord_430307, baseEnd_430307] using wordTrace_append hprefix tailTrace_430307
  have hstable : (prefixWord ++ tailWord_430307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430307).length < 2 ^ (prefixWord ++ tailWord_430307).sum := by decide
  have hdescent : baseEnd_430307 < baseStart_430307 := by decide
  rcases family_descends (prefixWord ++ tailWord_430307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430346 : List Nat := [3, 1, 2, 2, 1, 1, 2, 1, 4, 5]
def baseStart_430346 : Nat := 118140960795 + 430346 * 2 ^ 59
def prefixEnd_430346 : Nat := 4983230072969 + 3 ^ 40 * 430346 * 2
def baseEnd_430346 : Nat := 147316230493252335330587

theorem tailTrace_430346 : CollatzResearch.WordTrace tailWord_430346 prefixEnd_430346 147316230493252335330587 := by
  unfold tailWord_430346
  simp only [CollatzResearch.WordTrace]
  refine ⟨3924002024734353522623723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10464005399291609393663261 3924002024734353522623723)
  ·
    refine ⟨5886003037101530283935585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3924002024734353522623723 5886003037101530283935585)
    ·
      refine ⟨4414502277826147712951689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5886003037101530283935585 4414502277826147712951689)
      ·
        refine ⟨3310876708369610784713767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4414502277826147712951689 3310876708369610784713767)
        ·
          refine ⟨4966315062554416177070651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3310876708369610784713767 4966315062554416177070651)
          ·
            refine ⟨7449472593831624265605977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4966315062554416177070651 7449472593831624265605977)
            ·
              refine ⟨5587104445373718199204483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7449472593831624265605977 5587104445373718199204483)
              ·
                refine ⟨8380656668060577298806725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5587104445373718199204483 8380656668060577298806725)
                ·
                  refine ⟨1571373125261358243526261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8380656668060577298806725 1571373125261358243526261)
                  ·
                    refine ⟨147316230493252335330587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1571373125261358243526261 147316230493252335330587)
                    ·
                      rfl

theorem cell22_430346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_430346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_430346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_430346 prefixEnd_430346 := by exact prefixLift 430346
  have htrace : WordTrace (prefixWord ++ tailWord_430346) baseStart_430346 baseEnd_430346 := by
    simpa [prefixWord, tailWord_430346, baseEnd_430346] using wordTrace_append hprefix tailTrace_430346
  have hstable : (prefixWord ++ tailWord_430346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430346).length < 2 ^ (prefixWord ++ tailWord_430346).sum := by decide
  have hdescent : baseEnd_430346 < baseStart_430346 := by decide
  rcases family_descends (prefixWord ++ tailWord_430346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430365 : List Nat := [1, 4, 2, 3, 2, 1, 1, 3, 5]
def baseStart_430365 : Nat := 118140960795 + 430365 * 2 ^ 59
def prefixEnd_430365 : Nat := 4983230072969 + 3 ^ 40 * 430365 * 2
def baseEnd_430365 : Nat := 49107578193847539701843

theorem tailTrace_430365 : CollatzResearch.WordTrace tailWord_430365 prefixEnd_430365 49107578193847539701843 := by
  unfold tailWord_430365
  simp only [CollatzResearch.WordTrace]
  refine ⟨15696701085868580335436549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10464467390579053556957699 15696701085868580335436549)
  ·
    refine ⟨2943131453600358812894353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15696701085868580335436549 2943131453600358812894353)
    ·
      refine ⟨2207348590200269109670765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2943131453600358812894353 2207348590200269109670765)
      ·
        refine ⟨827755721325100916126537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2207348590200269109670765 827755721325100916126537)
        ·
          refine ⟨620816790993825687094903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 827755721325100916126537 620816790993825687094903)
          ·
            refine ⟨931225186490738530642355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 620816790993825687094903 931225186490738530642355)
            ·
              refine ⟨1396837779736107795963533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 931225186490738530642355 1396837779736107795963533)
              ·
                refine ⟨523814167401040423486325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1396837779736107795963533 523814167401040423486325)
                ·
                  refine ⟨49107578193847539701843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 523814167401040423486325 49107578193847539701843)
                  ·
                    rfl

theorem cell22_430365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 3, 5].length) (baseStart_430365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_430365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_430365 prefixEnd_430365 := by exact prefixLift 430365
  have htrace : WordTrace (prefixWord ++ tailWord_430365) baseStart_430365 baseEnd_430365 := by
    simpa [prefixWord, tailWord_430365, baseEnd_430365] using wordTrace_append hprefix tailTrace_430365
  have hstable : (prefixWord ++ tailWord_430365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430365).length < 2 ^ (prefixWord ++ tailWord_430365).sum := by decide
  have hdescent : baseEnd_430365 < baseStart_430365 := by decide
  rcases family_descends (prefixWord ++ tailWord_430365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430408 : List Nat := [2, 1, 3, 1, 1, 2, 2, 3, 4, 3]
def baseStart_430408 : Nat := 118140960795 + 430408 * 2 ^ 59
def prefixEnd_430408 : Nat := 4983230072969 + 3 ^ 40 * 430408 * 2
def baseEnd_430408 : Nat := 147337454360304840280397

theorem tailTrace_430408 : CollatzResearch.WordTrace tailWord_430408 prefixEnd_430408 147337454360304840280397 := by
  unfold tailWord_430408
  simp only [CollatzResearch.WordTrace]
  refine ⟨7849134712356399339625939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10465512949808532452834585 7849134712356399339625939)
  ·
    refine ⟨11773702068534599009438909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7849134712356399339625939 11773702068534599009438909)
    ·
      refine ⟨4415138275700474628539591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11773702068534599009438909 4415138275700474628539591)
      ·
        refine ⟨6622707413550711942809387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4415138275700474628539591 6622707413550711942809387)
        ·
          refine ⟨9934061120326067914214081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6622707413550711942809387 9934061120326067914214081)
          ·
            refine ⟨7450545840244550935660561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9934061120326067914214081 7450545840244550935660561)
            ·
              refine ⟨5587909380183413201745421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7450545840244550935660561 5587909380183413201745421)
              ·
                refine ⟨2095466017568779950654533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5587909380183413201745421 2095466017568779950654533)
                ·
                  refine ⟨392899878294146240747725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2095466017568779950654533 392899878294146240747725)
                  ·
                    refine ⟨147337454360304840280397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 392899878294146240747725 147337454360304840280397)
                    ·
                      rfl

theorem cell22_430408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 4, 3].length) (baseStart_430408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_430408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_430408 prefixEnd_430408 := by exact prefixLift 430408
  have htrace : WordTrace (prefixWord ++ tailWord_430408) baseStart_430408 baseEnd_430408 := by
    simpa [prefixWord, tailWord_430408, baseEnd_430408] using wordTrace_append hprefix tailTrace_430408
  have hstable : (prefixWord ++ tailWord_430408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430408).length < 2 ^ (prefixWord ++ tailWord_430408).sum := by decide
  have hdescent : baseEnd_430408 < baseStart_430408 := by decide
  rcases family_descends (prefixWord ++ tailWord_430408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430440 : List Nat := [2, 1, 4, 2, 2, 1, 3, 1, 2, 4]
def baseStart_430440 : Nat := 118140960795 + 430440 * 2 ^ 59
def prefixEnd_430440 : Nat := 4983230072969 + 3 ^ 40 * 430440 * 2
def baseEnd_430440 : Nat := 147348408614267423480299

theorem tailTrace_430440 : CollatzResearch.WordTrace tailWord_430440 prefixEnd_430440 147348408614267423480299 := by
  unfold tailWord_430440
  simp only [CollatzResearch.WordTrace]
  refine ⟨7849718280298434072208387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10466291040397912096277849 7849718280298434072208387)
  ·
    refine ⟨11774577420447651108312581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7849718280298434072208387 11774577420447651108312581)
    ·
      refine ⟨2207733266333934582808609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11774577420447651108312581 2207733266333934582808609)
      ·
        refine ⟨1655799949750450937106457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2207733266333934582808609 1655799949750450937106457)
        ·
          refine ⟨1241849962312838202829843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1655799949750450937106457 1241849962312838202829843)
          ·
            refine ⟨1862774943469257304244765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1241849962312838202829843 1862774943469257304244765)
            ·
              refine ⟨698540603800971489091787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1862774943469257304244765 698540603800971489091787)
              ·
                refine ⟨1047810905701457233637681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 698540603800971489091787 1047810905701457233637681)
                ·
                  refine ⟨785858179276092925228261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1047810905701457233637681 785858179276092925228261)
                  ·
                    refine ⟨147348408614267423480299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 785858179276092925228261 147348408614267423480299)
                    ·
                      rfl

theorem cell22_430440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_430440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_430440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_430440 prefixEnd_430440 := by exact prefixLift 430440
  have htrace : WordTrace (prefixWord ++ tailWord_430440) baseStart_430440 baseEnd_430440 := by
    simpa [prefixWord, tailWord_430440, baseEnd_430440] using wordTrace_append hprefix tailTrace_430440
  have hstable : (prefixWord ++ tailWord_430440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430440).length < 2 ^ (prefixWord ++ tailWord_430440).sum := by decide
  have hdescent : baseEnd_430440 < baseStart_430440 := by decide
  rcases family_descends (prefixWord ++ tailWord_430440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430451 : List Nat := [1, 1, 1, 2, 2, 1, 2, 2, 4, 6]
def baseStart_430451 : Nat := 118140960795 + 430451 * 2 ^ 59
def prefixEnd_430451 : Nat := 4983230072969 + 3 ^ 40 * 430451 * 2
def baseEnd_430451 : Nat := 147352174139067061455265

theorem tailTrace_430451 : CollatzResearch.WordTrace tailWord_430451 prefixEnd_430451 147352174139067061455265 := by
  unfold tailWord_430451
  simp only [CollatzResearch.WordTrace]
  refine ⟨15699837763557017023067207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10466558509038011348711471 15699837763557017023067207)
  ·
    refine ⟨23549756645335525534600811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15699837763557017023067207 23549756645335525534600811)
    ·
      refine ⟨35324634968003288301901217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23549756645335525534600811 35324634968003288301901217)
      ·
        refine ⟨26493476226002466226425913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35324634968003288301901217 26493476226002466226425913)
        ·
          refine ⟨19870107169501849669819435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26493476226002466226425913 19870107169501849669819435)
          ·
            refine ⟨29805160754252774504729153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19870107169501849669819435 29805160754252774504729153)
            ·
              refine ⟨22353870565689580878546865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29805160754252774504729153 22353870565689580878546865)
              ·
                refine ⟨16765402924267185658910149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22353870565689580878546865 16765402924267185658910149)
                ·
                  refine ⟨3143513048300097311045653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16765402924267185658910149 3143513048300097311045653)
                  ·
                    refine ⟨147352174139067061455265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3143513048300097311045653 147352174139067061455265)
                    ·
                      rfl

theorem cell22_430451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 6].length) (baseStart_430451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_430451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_430451 prefixEnd_430451 := by exact prefixLift 430451
  have htrace : WordTrace (prefixWord ++ tailWord_430451) baseStart_430451 baseEnd_430451 := by
    simpa [prefixWord, tailWord_430451, baseEnd_430451] using wordTrace_append hprefix tailTrace_430451
  have hstable : (prefixWord ++ tailWord_430451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430451).length < 2 ^ (prefixWord ++ tailWord_430451).sum := by decide
  have hdescent : baseEnd_430451 < baseStart_430451 := by decide
  rcases family_descends (prefixWord ++ tailWord_430451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430543 : List Nat := [1, 1, 2, 1, 1, 4, 1, 5, 1, 5]
def baseStart_430543 : Nat := 118140960795 + 430543 * 2 ^ 59
def prefixEnd_430543 : Nat := 4983230072969 + 3 ^ 40 * 430543 * 2
def baseEnd_430543 : Nat := 147383667619209488154983

theorem tailTrace_430543 : CollatzResearch.WordTrace tailWord_430543 prefixEnd_430543 147383667619209488154983 := by
  unfold tailWord_430543
  simp only [CollatzResearch.WordTrace]
  refine ⟨15703193279223716735416283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10468795519482477823610855 15703193279223716735416283)
  ·
    refine ⟨23554789918835575103124425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15703193279223716735416283 23554789918835575103124425)
    ·
      refine ⟨17666092439126681327343319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23554789918835575103124425 17666092439126681327343319)
      ·
        refine ⟨26499138658690021991014979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17666092439126681327343319 26499138658690021991014979)
        ·
          refine ⟨39748707988035032986522469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26499138658690021991014979 39748707988035032986522469)
          ·
            refine ⟨7452882747756568684972963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39748707988035032986522469 7452882747756568684972963)
            ·
              refine ⟨11179324121634853027459445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7452882747756568684972963 11179324121634853027459445)
              ·
                refine ⟨1048061636403267471324323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11179324121634853027459445 1048061636403267471324323)
                ·
                  refine ⟨1572092454604901206986485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1048061636403267471324323 1572092454604901206986485)
                  ·
                    refine ⟨147383667619209488154983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1572092454604901206986485 147383667619209488154983)
                    ·
                      rfl

theorem cell22_430543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5, 1, 5].length) (baseStart_430543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_430543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_430543 prefixEnd_430543 := by exact prefixLift 430543
  have htrace : WordTrace (prefixWord ++ tailWord_430543) baseStart_430543 baseEnd_430543 := by
    simpa [prefixWord, tailWord_430543, baseEnd_430543] using wordTrace_append hprefix tailTrace_430543
  have hstable : (prefixWord ++ tailWord_430543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430543).length < 2 ^ (prefixWord ++ tailWord_430543).sum := by decide
  have hdescent : baseEnd_430543 < baseStart_430543 := by decide
  rcases family_descends (prefixWord ++ tailWord_430543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430577 : List Nat := [1, 2, 2, 2, 3, 1, 4, 2, 2, 3]
def baseStart_430577 : Nat := 118140960795 + 430577 * 2 ^ 59
def prefixEnd_430577 : Nat := 4983230072969 + 3 ^ 40 * 430577 * 2
def baseEnd_430577 : Nat := 147395306514044732804879

theorem tailTrace_430577 : CollatzResearch.WordTrace tailWord_430577 prefixEnd_430577 147395306514044732804879 := by
  unfold tailWord_430577
  simp only [CollatzResearch.WordTrace]
  refine ⟨15704433361100540542153985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10469622240733693694769323 15704433361100540542153985)
  ·
    refine ⟨11778325020825405406615489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15704433361100540542153985 11778325020825405406615489)
    ·
      refine ⟨8833743765619054054961617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11778325020825405406615489 8833743765619054054961617)
      ·
        refine ⟨6625307824214290541221213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8833743765619054054961617 6625307824214290541221213)
        ·
          refine ⟨2484490434080358952957955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6625307824214290541221213 2484490434080358952957955)
          ·
            refine ⟨3726735651120538429436933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2484490434080358952957955 3726735651120538429436933)
            ·
              refine ⟨698762934585100955519425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3726735651120538429436933 698762934585100955519425)
              ·
                refine ⟨524072200938825716639569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 698762934585100955519425 524072200938825716639569)
                ·
                  refine ⟨393054150704119287479677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 524072200938825716639569 393054150704119287479677)
                  ·
                    refine ⟨147395306514044732804879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 393054150704119287479677 147395306514044732804879)
                    ·
                      rfl

theorem cell22_430577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 2, 2, 3].length) (baseStart_430577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_430577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_430577 prefixEnd_430577 := by exact prefixLift 430577
  have htrace : WordTrace (prefixWord ++ tailWord_430577) baseStart_430577 baseEnd_430577 := by
    simpa [prefixWord, tailWord_430577, baseEnd_430577] using wordTrace_append hprefix tailTrace_430577
  have hstable : (prefixWord ++ tailWord_430577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430577).length < 2 ^ (prefixWord ++ tailWord_430577).sum := by decide
  have hdescent : baseEnd_430577 < baseStart_430577 := by decide
  rcases family_descends (prefixWord ++ tailWord_430577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430588 : List Nat := [2, 2, 2, 1, 2, 1, 1, 2, 2, 7]
def baseStart_430588 : Nat := 118140960795 + 430588 * 2 ^ 59
def prefixEnd_430588 : Nat := 4983230072969 + 3 ^ 40 * 430588 * 2
def baseEnd_430588 : Nat := 147399072038844370779845

theorem tailTrace_430588 : CollatzResearch.WordTrace tailWord_430588 prefixEnd_430588 147399072038844370779845 := by
  unfold tailWord_430588
  simp only [CollatzResearch.WordTrace]
  refine ⟨7852417282030344710402209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10469889709373792947202945 7852417282030344710402209)
  ·
    refine ⟨5889312961522758532801657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7852417282030344710402209 5889312961522758532801657)
    ·
      refine ⟨4416984721142068899601243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5889312961522758532801657 4416984721142068899601243)
      ·
        refine ⟨6625477081713103349401865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4416984721142068899601243 6625477081713103349401865)
        ·
          refine ⟨4969107811284827512051399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6625477081713103349401865 4969107811284827512051399)
          ·
            refine ⟨7453661716927241268077099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4969107811284827512051399 7453661716927241268077099)
            ·
              refine ⟨11180492575390861902115649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7453661716927241268077099 11180492575390861902115649)
              ·
                refine ⟨8385369431543146426586737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11180492575390861902115649 8385369431543146426586737)
                ·
                  refine ⟨6289027073657359819940053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8385369431543146426586737 6289027073657359819940053)
                  ·
                    refine ⟨147399072038844370779845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6289027073657359819940053 147399072038844370779845)
                    ·
                      rfl

theorem cell22_430588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_430588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_430588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_430588 prefixEnd_430588 := by exact prefixLift 430588
  have htrace : WordTrace (prefixWord ++ tailWord_430588) baseStart_430588 baseEnd_430588 := by
    simpa [prefixWord, tailWord_430588, baseEnd_430588] using wordTrace_append hprefix tailTrace_430588
  have hstable : (prefixWord ++ tailWord_430588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430588).length < 2 ^ (prefixWord ++ tailWord_430588).sum := by decide
  have hdescent : baseEnd_430588 < baseStart_430588 := by decide
  rcases family_descends (prefixWord ++ tailWord_430588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430594 : List Nat := [3, 4, 1, 2, 2, 1, 2, 1, 1, 5]
def baseStart_430594 : Nat := 118140960795 + 430594 * 2 ^ 59
def prefixEnd_430594 : Nat := 4983230072969 + 3 ^ 40 * 430594 * 2
def baseEnd_430594 : Nat := 147401125961462355129827

theorem tailTrace_430594 : CollatzResearch.WordTrace tailWord_430594 prefixEnd_430594 147401125961462355129827 := by
  unfold tailWord_430594
  simp only [CollatzResearch.WordTrace]
  refine ⟨3926263350509738111380709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10470035601359301630348557 3926263350509738111380709)
  ·
    refine ⟨736174378220575895883883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3926263350509738111380709 736174378220575895883883)
    ·
      refine ⟨1104261567330863843825825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 736174378220575895883883 1104261567330863843825825)
      ·
        refine ⟨828196175498147882869369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1104261567330863843825825 828196175498147882869369)
        ·
          refine ⟨621147131623610912152027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 828196175498147882869369 621147131623610912152027)
          ·
            refine ⟨931720697435416368228041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 621147131623610912152027 931720697435416368228041)
            ·
              refine ⟨698790523076562276171031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 931720697435416368228041 698790523076562276171031)
              ·
                refine ⟨1048185784614843414256547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 698790523076562276171031 1048185784614843414256547)
                ·
                  refine ⟨1572278676922265121384821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1048185784614843414256547 1572278676922265121384821)
                  ·
                    refine ⟨147401125961462355129827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1572278676922265121384821 147401125961462355129827)
                    ·
                      rfl

theorem cell22_430594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_430594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_430594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_430594 prefixEnd_430594 := by exact prefixLift 430594
  have htrace : WordTrace (prefixWord ++ tailWord_430594) baseStart_430594 baseEnd_430594 := by
    simpa [prefixWord, tailWord_430594, baseEnd_430594] using wordTrace_append hprefix tailTrace_430594
  have hstable : (prefixWord ++ tailWord_430594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430594).length < 2 ^ (prefixWord ++ tailWord_430594).sum := by decide
  have hdescent : baseEnd_430594 < baseStart_430594 := by decide
  rcases family_descends (prefixWord ++ tailWord_430594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430628 : List Nat := [2, 3, 1, 5, 2, 1, 1, 2, 2, 3]
def baseStart_430628 : Nat := 118140960795 + 430628 * 2 ^ 59
def prefixEnd_430628 : Nat := 4983230072969 + 3 ^ 40 * 430628 * 2
def baseEnd_430628 : Nat := 147412764856297599779723

theorem tailTrace_430628 : CollatzResearch.WordTrace tailWord_430628 prefixEnd_430628 147412764856297599779723 := by
  unfold tailWord_430628
  simp only [CollatzResearch.WordTrace]
  refine ⟨7853146741957888126130269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10470862322610517501507025 7853146741957888126130269)
  ·
    refine ⟨2944930028234208047298851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7853146741957888126130269 2944930028234208047298851)
    ·
      refine ⟨4417395042351312070948277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2944930028234208047298851 4417395042351312070948277)
      ·
        refine ⟨414130785220435506651401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4417395042351312070948277 414130785220435506651401)
        ·
          refine ⟨310598088915326629988551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 414130785220435506651401 310598088915326629988551)
          ·
            refine ⟨465897133372989944982827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310598088915326629988551 465897133372989944982827)
            ·
              refine ⟨698845700059484917474241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 465897133372989944982827 698845700059484917474241)
              ·
                refine ⟨524134275044613688105681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 698845700059484917474241 524134275044613688105681)
                ·
                  refine ⟨393100706283460266079261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 524134275044613688105681 393100706283460266079261)
                  ·
                    refine ⟨147412764856297599779723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 393100706283460266079261 147412764856297599779723)
                    ·
                      rfl

theorem cell22_430628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 2, 2, 3].length) (baseStart_430628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_430628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_430628 prefixEnd_430628 := by exact prefixLift 430628
  have htrace : WordTrace (prefixWord ++ tailWord_430628) baseStart_430628 baseEnd_430628 := by
    simpa [prefixWord, tailWord_430628, baseEnd_430628] using wordTrace_append hprefix tailTrace_430628
  have hstable : (prefixWord ++ tailWord_430628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430628).length < 2 ^ (prefixWord ++ tailWord_430628).sum := by decide
  have hdescent : baseEnd_430628 < baseStart_430628 := by decide
  rcases family_descends (prefixWord ++ tailWord_430628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430650 : List Nat := [3, 1, 1, 1, 3, 3, 2, 1, 2, 5]
def baseStart_430650 : Nat := 118140960795 + 430650 * 2 ^ 59
def prefixEnd_430650 : Nat := 4983230072969 + 3 ^ 40 * 430650 * 2
def baseEnd_430650 : Nat := 147420295905896875729655

theorem tailTrace_430650 : CollatzResearch.WordTrace tailWord_430650 prefixEnd_430650 147420295905896875729655 := by
  unfold tailWord_430650
  simp only [CollatzResearch.WordTrace]
  refine ⟨3926773972459018502390351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10471397259890716006374269 3926773972459018502390351)
  ·
    refine ⟨5890160958688527753585527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3926773972459018502390351 5890160958688527753585527)
    ·
      refine ⟨8835241438032791630378291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5890160958688527753585527 8835241438032791630378291)
      ·
        refine ⟨13252862157049187445567437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8835241438032791630378291 13252862157049187445567437)
        ·
          refine ⟨4969823308893445292087789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13252862157049187445567437 4969823308893445292087789)
          ·
            refine ⟨1863683740835041984532921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4969823308893445292087789 1863683740835041984532921)
            ·
              refine ⟨1397762805626281488399691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1863683740835041984532921 1397762805626281488399691)
              ·
                refine ⟨2096644208439422232599537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1397762805626281488399691 2096644208439422232599537)
                ·
                  refine ⟨1572483156329566674449653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2096644208439422232599537 1572483156329566674449653)
                  ·
                    refine ⟨147420295905896875729655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1572483156329566674449653 147420295905896875729655)
                    ·
                      rfl

theorem cell22_430650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 2, 5].length) (baseStart_430650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_430650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_430650 prefixEnd_430650 := by exact prefixLift 430650
  have htrace : WordTrace (prefixWord ++ tailWord_430650) baseStart_430650 baseEnd_430650 := by
    simpa [prefixWord, tailWord_430650, baseEnd_430650] using wordTrace_append hprefix tailTrace_430650
  have hstable : (prefixWord ++ tailWord_430650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430650).length < 2 ^ (prefixWord ++ tailWord_430650).sum := by decide
  have hdescent : baseEnd_430650 < baseStart_430650 := by decide
  rcases family_descends (prefixWord ++ tailWord_430650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430690 : List Nat := [3, 3, 2, 3, 1, 1, 3, 2, 1, 3]
def baseStart_430690 : Nat := 118140960795 + 430690 * 2 ^ 59
def prefixEnd_430690 : Nat := 4983230072969 + 3 ^ 40 * 430690 * 2
def baseEnd_430690 : Nat := 147433988723350104729533

theorem tailTrace_430690 : CollatzResearch.WordTrace tailWord_430690 prefixEnd_430690 147433988723350104729533 := by
  unfold tailWord_430690
  simp only [CollatzResearch.WordTrace]
  refine ⟨3927138702422790210254381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10472369873127440560678349 3927138702422790210254381)
  ·
    refine ⟨1472677013408546328845393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3927138702422790210254381 1472677013408546328845393)
    ·
      refine ⟨1104507760056409746634045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1472677013408546328845393 1104507760056409746634045)
      ·
        refine ⟨414190410021153654987767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1104507760056409746634045 414190410021153654987767)
        ·
          refine ⟨621285615031730482481651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414190410021153654987767 621285615031730482481651)
          ·
            refine ⟨931928422547595723722477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 621285615031730482481651 931928422547595723722477)
            ·
              refine ⟨349473158455348396395929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 931928422547595723722477 349473158455348396395929)
              ·
                refine ⟨262104868841511297296947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 349473158455348396395929 262104868841511297296947)
                ·
                  refine ⟨393157303262266945945421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 262104868841511297296947 393157303262266945945421)
                  ·
                    refine ⟨147433988723350104729533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 393157303262266945945421 147433988723350104729533)
                    ·
                      rfl

theorem cell22_430690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_430690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_430690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_430690 prefixEnd_430690 := by exact prefixLift 430690
  have htrace : WordTrace (prefixWord ++ tailWord_430690) baseStart_430690 baseEnd_430690 := by
    simpa [prefixWord, tailWord_430690, baseEnd_430690] using wordTrace_append hprefix tailTrace_430690
  have hstable : (prefixWord ++ tailWord_430690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430690).length < 2 ^ (prefixWord ++ tailWord_430690).sum := by decide
  have hdescent : baseEnd_430690 < baseStart_430690 := by decide
  rcases family_descends (prefixWord ++ tailWord_430690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430712 : List Nat := [2, 1, 2, 1, 1, 1, 2, 7, 2, 3]
def baseStart_430712 : Nat := 118140960795 + 430712 * 2 ^ 59
def prefixEnd_430712 : Nat := 4983230072969 + 3 ^ 40 * 430712 * 2
def baseEnd_430712 : Nat := 147441519772949380679465

theorem tailTrace_430712 : CollatzResearch.WordTrace tailWord_430712 prefixEnd_430712 147441519772949380679465 := by
  unfold tailWord_430712
  simp only [CollatzResearch.WordTrace]
  refine ⟨7854678607805729299159195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10472904810407639065545593 7854678607805729299159195)
  ·
    refine ⟨11782017911708593948738793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7854678607805729299159195 11782017911708593948738793)
    ·
      refine ⟨8836513433781445461554095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11782017911708593948738793 8836513433781445461554095)
      ·
        refine ⟨13254770150672168192331143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8836513433781445461554095 13254770150672168192331143)
        ·
          refine ⟨19882155226008252288496715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13254770150672168192331143 19882155226008252288496715)
          ·
            refine ⟨29823232839012378432745073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19882155226008252288496715 29823232839012378432745073)
            ·
              refine ⟨22367424629259283824558805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29823232839012378432745073 22367424629259283824558805)
              ·
                refine ⟨524236514748264464638097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 22367424629259283824558805 524236514748264464638097)
                ·
                  refine ⟨393177386061198348478573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 524236514748264464638097 393177386061198348478573)
                  ·
                    refine ⟨147441519772949380679465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 393177386061198348478573 147441519772949380679465)
                    ·
                      rfl

theorem cell22_430712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 7, 2, 3].length) (baseStart_430712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_430712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_430712 prefixEnd_430712 := by exact prefixLift 430712
  have htrace : WordTrace (prefixWord ++ tailWord_430712) baseStart_430712 baseEnd_430712 := by
    simpa [prefixWord, tailWord_430712, baseEnd_430712] using wordTrace_append hprefix tailTrace_430712
  have hstable : (prefixWord ++ tailWord_430712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430712).length < 2 ^ (prefixWord ++ tailWord_430712).sum := by decide
  have hdescent : baseEnd_430712 < baseStart_430712 := by decide
  rcases family_descends (prefixWord ++ tailWord_430712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430725 : List Nat := [1, 3, 1, 1, 4, 2, 2, 8]
def baseStart_430725 : Nat := 118140960795 + 430725 * 2 ^ 59
def prefixEnd_430725 : Nat := 4983230072969 + 3 ^ 40 * 430725 * 2
def baseEnd_430725 : Nat := 16382885548735742233825

theorem tailTrace_430725 : CollatzResearch.WordTrace tailWord_430725 prefixEnd_430725 16382885548735742233825 := by
  unfold tailWord_430725
  simp only [CollatzResearch.WordTrace]
  refine ⟨15709831364564361818541629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10473220909709574545694419 15709831364564361818541629)
  ·
    refine ⟨5891186761711635681953111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15709831364564361818541629 5891186761711635681953111)
    ·
      refine ⟨8836780142567453522929667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5891186761711635681953111 8836780142567453522929667)
      ·
        refine ⟨13255170213851180284394501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8836780142567453522929667 13255170213851180284394501)
        ·
          refine ⟨2485344415097096303323969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13255170213851180284394501 2485344415097096303323969)
          ·
            refine ⟨1864008311322822227492977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2485344415097096303323969 1864008311322822227492977)
            ·
              refine ⟨1398006233492116670619733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1864008311322822227492977 1398006233492116670619733)
              ·
                refine ⟨16382885548735742233825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1398006233492116670619733 16382885548735742233825)
                ·
                  rfl

theorem cell22_430725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 8].length) (baseStart_430725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_430725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_430725 prefixEnd_430725 := by exact prefixLift 430725
  have htrace : WordTrace (prefixWord ++ tailWord_430725) baseStart_430725 baseEnd_430725 := by
    simpa [prefixWord, tailWord_430725, baseEnd_430725] using wordTrace_append hprefix tailTrace_430725
  have hstable : (prefixWord ++ tailWord_430725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430725).length < 2 ^ (prefixWord ++ tailWord_430725).sum := by decide
  have hdescent : baseEnd_430725 < baseStart_430725 := by decide
  rcases family_descends (prefixWord ++ tailWord_430725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430727 : List Nat := [1, 1, 4, 2, 1, 2, 4, 1, 2, 4]
def baseStart_430727 : Nat := 118140960795 + 430727 * 2 ^ 59
def prefixEnd_430727 : Nat := 4983230072969 + 3 ^ 40 * 430727 * 2
def baseEnd_430727 : Nat := 147446654579494341554419

theorem tailTrace_430727 : CollatzResearch.WordTrace tailWord_430727 prefixEnd_430727 147446654579494341554419 := by
  unfold tailWord_430727
  simp only [CollatzResearch.WordTrace]
  refine ⟨15709904310557116160114435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10473269540371410773409623 15709904310557116160114435)
  ·
    refine ⟨23564856465835674240171653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15709904310557116160114435 23564856465835674240171653)
    ·
      refine ⟨4418410587344188920032185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23564856465835674240171653 4418410587344188920032185)
      ·
        refine ⟨3313807940508141690024139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4418410587344188920032185 3313807940508141690024139)
        ·
          refine ⟨4970711910762212535036209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3313807940508141690024139 4970711910762212535036209)
          ·
            refine ⟨3728033933071659401277157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4970711910762212535036209 3728033933071659401277157)
            ·
              refine ⟨699006362450936137739467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3728033933071659401277157 699006362450936137739467)
              ·
                refine ⟨1048509543676404206609201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 699006362450936137739467 1048509543676404206609201)
                ·
                  refine ⟨786382157757303154956901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1048509543676404206609201 786382157757303154956901)
                  ·
                    refine ⟨147446654579494341554419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 786382157757303154956901 147446654579494341554419)
                    ·
                      rfl

theorem cell22_430727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 1, 2, 4].length) (baseStart_430727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_430727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_430727 prefixEnd_430727 := by exact prefixLift 430727
  have htrace : WordTrace (prefixWord ++ tailWord_430727) baseStart_430727 baseEnd_430727 := by
    simpa [prefixWord, tailWord_430727, baseEnd_430727] using wordTrace_append hprefix tailTrace_430727
  have hstable : (prefixWord ++ tailWord_430727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430727).length < 2 ^ (prefixWord ++ tailWord_430727).sum := by decide
  have hdescent : baseEnd_430727 < baseStart_430727 := by decide
  rcases family_descends (prefixWord ++ tailWord_430727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430757 : List Nat := [1, 3, 1, 2, 1, 2, 1, 5, 3, 3]
def baseStart_430757 : Nat := 118140960795 + 430757 * 2 ^ 59
def prefixEnd_430757 : Nat := 4983230072969 + 3 ^ 40 * 430757 * 2
def baseEnd_430757 : Nat := 147456924192584263304327

theorem tailTrace_430757 : CollatzResearch.WordTrace tailWord_430757 prefixEnd_430757 147456924192584263304327 := by
  unfold tailWord_430757
  simp only [CollatzResearch.WordTrace]
  refine ⟨15710998500448431283706525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10473999000298954189137683 15710998500448431283706525)
  ·
    refine ⟨5891624437668161731389947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15710998500448431283706525 5891624437668161731389947)
    ·
      refine ⟨8837436656502242597084921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5891624437668161731389947 8837436656502242597084921)
      ·
        refine ⟨6628077492376681947813691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8837436656502242597084921 6628077492376681947813691)
        ·
          refine ⟨9942116238565022921720537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6628077492376681947813691 9942116238565022921720537)
          ·
            refine ⟨7456587178923767191290403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9942116238565022921720537 7456587178923767191290403)
            ·
              refine ⟨11184880768385650786935605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7456587178923767191290403 11184880768385650786935605)
              ·
                refine ⟨1048582572036154761275213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11184880768385650786935605 1048582572036154761275213)
                ·
                  refine ⟨393218464513558035478205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1048582572036154761275213 393218464513558035478205)
                  ·
                    refine ⟨147456924192584263304327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 393218464513558035478205 147456924192584263304327)
                    ·
                      rfl

theorem cell22_430757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5, 3, 3].length) (baseStart_430757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_430757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_430757 prefixEnd_430757 := by exact prefixLift 430757
  have htrace : WordTrace (prefixWord ++ tailWord_430757) baseStart_430757 baseEnd_430757 := by
    simpa [prefixWord, tailWord_430757, baseEnd_430757] using wordTrace_append hprefix tailTrace_430757
  have hstable : (prefixWord ++ tailWord_430757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430757).length < 2 ^ (prefixWord ++ tailWord_430757).sum := by decide
  have hdescent : baseEnd_430757 < baseStart_430757 := by decide
  rcases family_descends (prefixWord ++ tailWord_430757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430770 : List Nat := [3, 2, 1, 1, 1, 2, 1, 2, 9]
def baseStart_430770 : Nat := 118140960795 + 430770 * 2 ^ 59
def prefixEnd_430770 : Nat := 4983230072969 + 3 ^ 40 * 430770 * 2
def baseEnd_430770 : Nat := 49153791452752187576429

theorem tailTrace_430770 : CollatzResearch.WordTrace tailWord_430770 prefixEnd_430770 49153791452752187576429 := by
  unfold tailWord_430770
  simp only [CollatzResearch.WordTrace]
  refine ⟨3927868162350333625982441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10474315099600889669286509 3927868162350333625982441)
  ·
    refine ⟨2945901121762750219486831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3927868162350333625982441 2945901121762750219486831)
    ·
      refine ⟨4418851682644125329230247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2945901121762750219486831 4418851682644125329230247)
      ·
        refine ⟨6628277523966187993845371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4418851682644125329230247 6628277523966187993845371)
        ·
          refine ⟨9942416285949281990768057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6628277523966187993845371 9942416285949281990768057)
          ·
            refine ⟨7456812214461961493076043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9942416285949281990768057 7456812214461961493076043)
            ·
              refine ⟨11185218321692942239614065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7456812214461961493076043 11185218321692942239614065)
              ·
                refine ⟨8388913741269706679710549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11185218321692942239614065 8388913741269706679710549)
                ·
                  refine ⟨49153791452752187576429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 8388913741269706679710549 49153791452752187576429)
                  ·
                    rfl

theorem cell22_430770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 9].length) (baseStart_430770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_430770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_430770 prefixEnd_430770 := by exact prefixLift 430770
  have htrace : WordTrace (prefixWord ++ tailWord_430770) baseStart_430770 baseEnd_430770 := by
    simpa [prefixWord, tailWord_430770, baseEnd_430770] using wordTrace_append hprefix tailTrace_430770
  have hstable : (prefixWord ++ tailWord_430770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430770).length < 2 ^ (prefixWord ++ tailWord_430770).sum := by decide
  have hdescent : baseEnd_430770 < baseStart_430770 := by decide
  rcases family_descends (prefixWord ++ tailWord_430770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430804 : List Nat := [2, 4, 1, 3, 2, 1, 1, 1, 7]
def baseStart_430804 : Nat := 118140960795 + 430804 * 2 ^ 59
def prefixEnd_430804 : Nat := 4983230072969 + 3 ^ 40 * 430804 * 2
def baseEnd_430804 : Nat := 49157671084363935793061

theorem tailTrace_430804 : CollatzResearch.WordTrace tailWord_430804 prefixEnd_430804 49157671084363935793061 := by
  unfold tailWord_430804
  simp only [CollatzResearch.WordTrace]
  refine ⟨7856356365639079155333733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10475141820852105540444977 7856356365639079155333733)
  ·
    refine ⟨1473066818557327341625075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7856356365639079155333733 1473066818557327341625075)
    ·
      refine ⟨2209600227835991012437613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1473066818557327341625075 2209600227835991012437613)
      ·
        refine ⟨828600085438496629664105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2209600227835991012437613 828600085438496629664105)
        ·
          refine ⟨621450064078872472248079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 828600085438496629664105 621450064078872472248079)
          ·
            refine ⟨932175096118308708372119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 621450064078872472248079 932175096118308708372119)
            ·
              refine ⟨1398262644177463062558179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 932175096118308708372119 1398262644177463062558179)
              ·
                refine ⟨2097393966266194593837269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1398262644177463062558179 2097393966266194593837269)
                ·
                  refine ⟨49157671084363935793061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2097393966266194593837269 49157671084363935793061)
                  ·
                    rfl

theorem cell22_430804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_430804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_430804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_430804 prefixEnd_430804 := by exact prefixLift 430804
  have htrace : WordTrace (prefixWord ++ tailWord_430804) baseStart_430804 baseEnd_430804 := by
    simpa [prefixWord, tailWord_430804, baseEnd_430804] using wordTrace_append hprefix tailTrace_430804
  have hstable : (prefixWord ++ tailWord_430804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430804).length < 2 ^ (prefixWord ++ tailWord_430804).sum := by decide
  have hdescent : baseEnd_430804 < baseStart_430804 := by decide
  rcases family_descends (prefixWord ++ tailWord_430804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430834 : List Nat := [3, 2, 1, 3, 1, 2, 1, 4, 1, 4]
def baseStart_430834 : Nat := 118140960795 + 430834 * 2 ^ 59
def prefixEnd_430834 : Nat := 4983230072969 + 3 ^ 40 * 430834 * 2
def baseEnd_430834 : Nat := 147483282866181729129091

theorem tailTrace_430834 : CollatzResearch.WordTrace tailWord_430834 prefixEnd_430834 147483282866181729129091 := by
  unfold tailWord_430834
  simp only [CollatzResearch.WordTrace]
  refine ⟨3928451730292368358564889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10475871280779648956173037 3928451730292368358564889)
  ·
    refine ⟨2946338797719276268923667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3928451730292368358564889 2946338797719276268923667)
    ·
      refine ⟨4419508196578914403385501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2946338797719276268923667 4419508196578914403385501)
      ·
        refine ⟨1657315573717092901269563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4419508196578914403385501 1657315573717092901269563)
        ·
          refine ⟨2485973360575639351904345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1657315573717092901269563 2485973360575639351904345)
          ·
            refine ⟨1864480020431729513928259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2485973360575639351904345 1864480020431729513928259)
            ·
              refine ⟨2796720030647594270892389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1864480020431729513928259 2796720030647594270892389)
              ·
                refine ⟨524385005746423925792323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2796720030647594270892389 524385005746423925792323)
                ·
                  refine ⟨786577508619635888688485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 524385005746423925792323 786577508619635888688485)
                  ·
                    refine ⟨147483282866181729129091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 786577508619635888688485 147483282866181729129091)
                    ·
                      rfl

theorem cell22_430834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 4, 1, 4].length) (baseStart_430834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_430834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_430834 prefixEnd_430834 := by exact prefixLift 430834
  have htrace : WordTrace (prefixWord ++ tailWord_430834) baseStart_430834 baseEnd_430834 := by
    simpa [prefixWord, tailWord_430834, baseEnd_430834] using wordTrace_append hprefix tailTrace_430834
  have hstable : (prefixWord ++ tailWord_430834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430834).length < 2 ^ (prefixWord ++ tailWord_430834).sum := by decide
  have hdescent : baseEnd_430834 < baseStart_430834 := by decide
  rcases family_descends (prefixWord ++ tailWord_430834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430894 : List Nat := [4, 1, 3, 2, 1, 1, 2, 8]
def baseStart_430894 : Nat := 118140960795 + 430894 * 2 ^ 59
def prefixEnd_430894 : Nat := 4983230072969 + 3 ^ 40 * 430894 * 2
def baseEnd_430894 : Nat := 16389313565817952514323

theorem tailTrace_430894 : CollatzResearch.WordTrace tailWord_430894 prefixEnd_430894 16389313565817952514323 := by
  unfold tailWord_430894
  simp only [CollatzResearch.WordTrace]
  refine ⟨1964499412619012960180467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10477330200634735787629157 1964499412619012960180467)
  ·
    refine ⟨2946749118928519440270701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1964499412619012960180467 2946749118928519440270701)
    ·
      refine ⟨1105030919598194790101513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2946749118928519440270701 1105030919598194790101513)
      ·
        refine ⟨828773189698646092576135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1105030919598194790101513 828773189698646092576135)
        ·
          refine ⟨1243159784547969138864203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 828773189698646092576135 1243159784547969138864203)
          ·
            refine ⟨1864739676821953708296305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1243159784547969138864203 1864739676821953708296305)
            ·
              refine ⟨1398554757616465281222229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1864739676821953708296305 1398554757616465281222229)
              ·
                refine ⟨16389313565817952514323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1398554757616465281222229 16389313565817952514323)
                ·
                  rfl

theorem cell22_430894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 8].length) (baseStart_430894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_430894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_430894 prefixEnd_430894 := by exact prefixLift 430894
  have htrace : WordTrace (prefixWord ++ tailWord_430894) baseStart_430894 baseEnd_430894 := by
    simpa [prefixWord, tailWord_430894, baseEnd_430894] using wordTrace_append hprefix tailTrace_430894
  have hstable : (prefixWord ++ tailWord_430894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430894).length < 2 ^ (prefixWord ++ tailWord_430894).sum := by decide
  have hdescent : baseEnd_430894 < baseStart_430894 := by decide
  rcases family_descends (prefixWord ++ tailWord_430894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430937 : List Nat := [1, 2, 1, 2, 2, 4, 1, 1, 1, 7]
def baseStart_430937 : Nat := 118140960795 + 430937 * 2 ^ 59
def prefixEnd_430937 : Nat := 4983230072969 + 3 ^ 40 * 430937 * 2
def baseEnd_430937 : Nat := 147518541871123793803775

theorem tailTrace_430937 : CollatzResearch.WordTrace tailWord_430937 prefixEnd_430937 147518541871123793803775 := by
  unfold tailWord_430937
  simp only [CollatzResearch.WordTrace]
  refine ⟨15717563639796322025259065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10478375759864214683506043 15717563639796322025259065)
  ·
    refine ⟨11788172729847241518944299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15717563639796322025259065 11788172729847241518944299)
    ·
      refine ⟨17682259094770862278416449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11788172729847241518944299 17682259094770862278416449)
      ·
        refine ⟨13261694321078146708812337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17682259094770862278416449 13261694321078146708812337)
        ·
          refine ⟨9946270740808610031609253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13261694321078146708812337 9946270740808610031609253)
          ·
            refine ⟨1864925763901614380926735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9946270740808610031609253 1864925763901614380926735)
            ·
              refine ⟨2797388645852421571390103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1864925763901614380926735 2797388645852421571390103)
              ·
                refine ⟨4196082968778632357085155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2797388645852421571390103 4196082968778632357085155)
                ·
                  refine ⟨6294124453167948535627733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4196082968778632357085155 6294124453167948535627733)
                  ·
                    refine ⟨147518541871123793803775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6294124453167948535627733 147518541871123793803775)
                    ·
                      rfl

theorem cell22_430937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 7].length) (baseStart_430937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_430937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_430937 prefixEnd_430937 := by exact prefixLift 430937
  have htrace : WordTrace (prefixWord ++ tailWord_430937) baseStart_430937 baseEnd_430937 := by
    simpa [prefixWord, tailWord_430937, baseEnd_430937] using wordTrace_append hprefix tailTrace_430937
  have hstable : (prefixWord ++ tailWord_430937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430937).length < 2 ^ (prefixWord ++ tailWord_430937).sum := by decide
  have hdescent : baseEnd_430937 < baseStart_430937 := by decide
  rcases family_descends (prefixWord ++ tailWord_430937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430984 : List Nat := [2, 1, 3, 3, 2, 1, 1, 3, 6]
def baseStart_430984 : Nat := 118140960795 + 430984 * 2 ^ 59
def prefixEnd_430984 : Nat := 4983230072969 + 3 ^ 40 * 430984 * 2
def baseEnd_430984 : Nat := 49178210310543779292877

theorem tailTrace_430984 : CollatzResearch.WordTrace tailWord_430984 prefixEnd_430984 49178210310543779292877 := by
  unfold tailWord_430984
  simp only [CollatzResearch.WordTrace]
  refine ⟨7859638935313024526110003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10479518580417366034813337 7859638935313024526110003)
  ·
    refine ⟨11789458402969536789165005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7859638935313024526110003 11789458402969536789165005)
    ·
      refine ⟨4421046901113576295936877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11789458402969536789165005 4421046901113576295936877)
      ·
        refine ⟨1657892587917591110976329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4421046901113576295936877 1657892587917591110976329)
        ·
          refine ⟨1243419440938193333232247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1657892587917591110976329 1243419440938193333232247)
          ·
            refine ⟨1865129161407289999848371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1243419440938193333232247 1865129161407289999848371)
            ·
              refine ⟨2797693742110934999772557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1865129161407289999848371 2797693742110934999772557)
              ·
                refine ⟨1049135153291600624914709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2797693742110934999772557 1049135153291600624914709)
                ·
                  refine ⟨49178210310543779292877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1049135153291600624914709 49178210310543779292877)
                  ·
                    rfl

theorem cell22_430984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 3, 6].length) (baseStart_430984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_430984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_430984 prefixEnd_430984 := by exact prefixLift 430984
  have htrace : WordTrace (prefixWord ++ tailWord_430984) baseStart_430984 baseEnd_430984 := by
    simpa [prefixWord, tailWord_430984, baseEnd_430984] using wordTrace_append hprefix tailTrace_430984
  have hstable : (prefixWord ++ tailWord_430984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430984).length < 2 ^ (prefixWord ++ tailWord_430984).sum := by decide
  have hdescent : baseEnd_430984 < baseStart_430984 := by decide
  rcases family_descends (prefixWord ++ tailWord_430984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431138 : List Nat := [3, 3, 1, 1, 1, 4, 1, 3, 1, 4]
def baseStart_431138 : Nat := 118140960795 + 431138 * 2 ^ 59
def prefixEnd_431138 : Nat := 4983230072969 + 3 ^ 40 * 431138 * 2
def baseEnd_431138 : Nat := 147587348278826269528159

theorem tailTrace_431138 : CollatzResearch.WordTrace tailWord_431138 prefixEnd_431138 147587348278826269528159 := by
  unfold tailWord_431138
  simp only [CollatzResearch.WordTrace]
  refine ⟨3931223678017033338331517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10483263141378755568884045 3931223678017033338331517)
  ·
    refine ⟨1474208879256387501874319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3931223678017033338331517 1474208879256387501874319)
    ·
      refine ⟨2211313318884581252811479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1474208879256387501874319 2211313318884581252811479)
      ·
        refine ⟨3316969978326871879217219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2211313318884581252811479 3316969978326871879217219)
        ·
          refine ⟨4975454967490307818825829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3316969978326871879217219 4975454967490307818825829)
          ·
            refine ⟨932897806404432716029843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4975454967490307818825829 932897806404432716029843)
            ·
              refine ⟨1399346709606649074044765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 932897806404432716029843 1399346709606649074044765)
              ·
                refine ⟨524755016102493402766787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1399346709606649074044765 524755016102493402766787)
                ·
                  refine ⟨787132524153740104150181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 524755016102493402766787 787132524153740104150181)
                  ·
                    refine ⟨147587348278826269528159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 787132524153740104150181 147587348278826269528159)
                    ·
                      rfl

theorem cell22_431138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_431138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_431138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_431138 prefixEnd_431138 := by exact prefixLift 431138
  have htrace : WordTrace (prefixWord ++ tailWord_431138) baseStart_431138 baseEnd_431138 := by
    simpa [prefixWord, tailWord_431138, baseEnd_431138] using wordTrace_append hprefix tailTrace_431138
  have hstable : (prefixWord ++ tailWord_431138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431138).length < 2 ^ (prefixWord ++ tailWord_431138).sum := by decide
  have hdescent : baseEnd_431138 < baseStart_431138 := by decide
  rcases family_descends (prefixWord ++ tailWord_431138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431320 : List Nat := [2, 1, 2, 2, 5, 1, 1, 1, 4, 3]
def baseStart_431320 : Nat := 118140960795 + 431320 * 2 ^ 59
def prefixEnd_431320 : Nat := 4983230072969 + 3 ^ 40 * 431320 * 2
def baseEnd_431320 : Nat := 147649650598238461477601

theorem tailTrace_431320 : CollatzResearch.WordTrace tailWord_431320 prefixEnd_431320 147649650598238461477601 := by
  unfold tailWord_431320
  simp only [CollatzResearch.WordTrace]
  refine ⟨7865766398704389218225707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10487688531605852290967609 7865766398704389218225707)
  ·
    refine ⟨11798649598056583827338561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7865766398704389218225707 11798649598056583827338561)
    ·
      refine ⟨8848987198542437870503921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11798649598056583827338561 8848987198542437870503921)
      ·
        refine ⟨6636740398906828402877941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8848987198542437870503921 6636740398906828402877941)
        ·
          refine ⟨622194412397515162769807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6636740398906828402877941 622194412397515162769807)
          ·
            refine ⟨933291618596272744154711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 622194412397515162769807 933291618596272744154711)
            ·
              refine ⟨1399937427894409116232067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 933291618596272744154711 1399937427894409116232067)
              ·
                refine ⟨2099906141841613674348101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1399937427894409116232067 2099906141841613674348101)
                ·
                  refine ⟨393732401595302563940269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2099906141841613674348101 393732401595302563940269)
                  ·
                    refine ⟨147649650598238461477601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 393732401595302563940269 147649650598238461477601)
                    ·
                      rfl

theorem cell22_431320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 4, 3].length) (baseStart_431320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_431320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_431320 prefixEnd_431320 := by exact prefixLift 431320
  have htrace : WordTrace (prefixWord ++ tailWord_431320) baseStart_431320 baseEnd_431320 := by
    simpa [prefixWord, tailWord_431320, baseEnd_431320] using wordTrace_append hprefix tailTrace_431320
  have hstable : (prefixWord ++ tailWord_431320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431320).length < 2 ^ (prefixWord ++ tailWord_431320).sum := by decide
  have hdescent : baseEnd_431320 < baseStart_431320 := by decide
  rcases family_descends (prefixWord ++ tailWord_431320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431395 : List Nat := [1, 1, 1, 4, 2, 3, 4, 1, 5]
def baseStart_431395 : Nat := 118140960795 + 431395 * 2 ^ 59
def prefixEnd_431395 : Nat := 4983230072969 + 3 ^ 40 * 431395 * 2
def baseEnd_431395 : Nat := 49225108210321088617457

theorem tailTrace_431395 : CollatzResearch.WordTrace tailWord_431395 prefixEnd_431395 49225108210321088617457 := by
  unfold tailWord_431395
  simp only [CollatzResearch.WordTrace]
  refine ⟨15734268272137066245431639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10489512181424710830287759 15734268272137066245431639)
  ·
    refine ⟨23601402408205599368147459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15734268272137066245431639 23601402408205599368147459)
    ·
      refine ⟨35402103612308399052221189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23601402408205599368147459 35402103612308399052221189)
      ·
        refine ⟨6637894427307824822291473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35402103612308399052221189 6637894427307824822291473)
        ·
          refine ⟨4978420820480868616718605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6637894427307824822291473 4978420820480868616718605)
          ·
            refine ⟨1866907807680325731269477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4978420820480868616718605 1866907807680325731269477)
            ·
              refine ⟨350045213940061074613027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1866907807680325731269477 350045213940061074613027)
              ·
                refine ⟨525067820910091611919541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 350045213940061074613027 525067820910091611919541)
                ·
                  refine ⟨49225108210321088617457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 525067820910091611919541 49225108210321088617457)
                  ·
                    rfl

theorem cell22_431395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4, 1, 5].length) (baseStart_431395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_431395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_431395 prefixEnd_431395 := by exact prefixLift 431395
  have htrace : WordTrace (prefixWord ++ tailWord_431395) baseStart_431395 baseEnd_431395 := by
    simpa [prefixWord, tailWord_431395, baseEnd_431395] using wordTrace_append hprefix tailTrace_431395
  have hstable : (prefixWord ++ tailWord_431395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431395).length < 2 ^ (prefixWord ++ tailWord_431395).sum := by decide
  have hdescent : baseEnd_431395 < baseStart_431395 := by decide
  rcases family_descends (prefixWord ++ tailWord_431395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431408 : List Nat := [2, 1, 1, 1, 2, 2, 5, 1, 3, 4]
def baseStart_431408 : Nat := 118140960795 + 431408 * 2 ^ 59
def prefixEnd_431408 : Nat := 4983230072969 + 3 ^ 40 * 431408 * 2
def baseEnd_431408 : Nat := 147679774796635565277331

theorem tailTrace_431408 : CollatzResearch.WordTrace tailWord_431408 prefixEnd_431408 147679774796635565277331 := by
  unfold tailWord_431408
  simp only [CollatzResearch.WordTrace]
  refine ⟨7867371210544984732827439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10489828280726646310436585 7867371210544984732827439)
  ·
    refine ⟨11801056815817477099241159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7867371210544984732827439 11801056815817477099241159)
    ·
      refine ⟨17701585223726215648861739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11801056815817477099241159 17701585223726215648861739)
      ·
        refine ⟨26552377835589323473292609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17701585223726215648861739 26552377835589323473292609)
        ·
          refine ⟨19914283376691992604969457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26552377835589323473292609 19914283376691992604969457)
          ·
            refine ⟨14935712532518994453727093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19914283376691992604969457 14935712532518994453727093)
            ·
              refine ⟨1400223049923655730036915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14935712532518994453727093 1400223049923655730036915)
              ·
                refine ⟨2100334574885483595055373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1400223049923655730036915 2100334574885483595055373)
                ·
                  refine ⟨787625465582056348145765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2100334574885483595055373 787625465582056348145765)
                  ·
                    refine ⟨147679774796635565277331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 787625465582056348145765 147679774796635565277331)
                    ·
                      rfl

theorem cell22_431408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 3, 4].length) (baseStart_431408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_431408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_431408 prefixEnd_431408 := by exact prefixLift 431408
  have htrace : WordTrace (prefixWord ++ tailWord_431408) baseStart_431408 baseEnd_431408 := by
    simpa [prefixWord, tailWord_431408, baseEnd_431408] using wordTrace_append hprefix tailTrace_431408
  have hstable : (prefixWord ++ tailWord_431408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431408).length < 2 ^ (prefixWord ++ tailWord_431408).sum := by decide
  have hdescent : baseEnd_431408 < baseStart_431408 := by decide
  rcases family_descends (prefixWord ++ tailWord_431408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431438 : List Nat := [4, 1, 1, 1, 1, 1, 3, 2, 3, 5]
def baseStart_431438 : Nat := 118140960795 + 431438 * 2 ^ 59
def prefixEnd_431438 : Nat := 4983230072969 + 3 ^ 40 * 431438 * 2
def baseEnd_431438 : Nat := 147690044409725487027239

theorem tailTrace_431438 : CollatzResearch.WordTrace tailWord_431438 prefixEnd_431438 147690044409725487027239 := by
  unfold tailWord_431438
  simp only [CollatzResearch.WordTrace]
  refine ⟨1966979576372660573655871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10490557740654189726164645 1966979576372660573655871)
  ·
    refine ⟨2950469364558990860483807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1966979576372660573655871 2950469364558990860483807)
    ·
      refine ⟨4425704046838486290725711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2950469364558990860483807 4425704046838486290725711)
      ·
        refine ⟨6638556070257729436088567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4425704046838486290725711 6638556070257729436088567)
        ·
          refine ⟨9957834105386594154132851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6638556070257729436088567 9957834105386594154132851)
          ·
            refine ⟨14936751158079891231199277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9957834105386594154132851 14936751158079891231199277)
            ·
              refine ⟨5601281684279959211699729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14936751158079891231199277 5601281684279959211699729)
              ·
                refine ⟨4200961263209969408774797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5601281684279959211699729 4200961263209969408774797)
                ·
                  refine ⟨1575360473703738528290549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4200961263209969408774797 1575360473703738528290549)
                  ·
                    refine ⟨147690044409725487027239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1575360473703738528290549 147690044409725487027239)
                    ·
                      rfl

theorem cell22_431438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_431438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_431438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_431438 prefixEnd_431438 := by exact prefixLift 431438
  have htrace : WordTrace (prefixWord ++ tailWord_431438) baseStart_431438 baseEnd_431438 := by
    simpa [prefixWord, tailWord_431438, baseEnd_431438] using wordTrace_append hprefix tailTrace_431438
  have hstable : (prefixWord ++ tailWord_431438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431438).length < 2 ^ (prefixWord ++ tailWord_431438).sum := by decide
  have hdescent : baseEnd_431438 < baseStart_431438 := by decide
  rcases family_descends (prefixWord ++ tailWord_431438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431440 : List Nat := [2, 1, 1, 1, 1, 5, 3, 4, 4]
def baseStart_431440 : Nat := 118140960795 + 431440 * 2 ^ 59
def prefixEnd_431440 : Nat := 4983230072969 + 3 ^ 40 * 431440 * 2
def baseEnd_431440 : Nat := 49230243016866049492411

theorem tailTrace_431440 : CollatzResearch.WordTrace tailWord_431440 prefixEnd_431440 49230243016866049492411 := by
  unfold tailWord_431440
  simp only [CollatzResearch.WordTrace]
  refine ⟨7867954778487019465409887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10490606371316025953879849 7867954778487019465409887)
  ·
    refine ⟨11801932167730529198114831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7867954778487019465409887 11801932167730529198114831)
    ·
      refine ⟨17702898251595793797172247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11801932167730529198114831 17702898251595793797172247)
      ·
        refine ⟨26554347377393690695758371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17702898251595793797172247 26554347377393690695758371)
        ·
          refine ⟨39831521066090536043637557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26554347377393690695758371 39831521066090536043637557)
          ·
            refine ⟨3734205099945987754091021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39831521066090536043637557 3734205099945987754091021)
            ·
              refine ⟨1400326912479745407784133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3734205099945987754091021 1400326912479745407784133)
              ·
                refine ⟨262561296089952263959525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1400326912479745407784133 262561296089952263959525)
                ·
                  refine ⟨49230243016866049492411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 262561296089952263959525 49230243016866049492411)
                  ·
                    rfl

theorem cell22_431440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 4, 4].length) (baseStart_431440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_431440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_431440 prefixEnd_431440 := by exact prefixLift 431440
  have htrace : WordTrace (prefixWord ++ tailWord_431440) baseStart_431440 baseEnd_431440 := by
    simpa [prefixWord, tailWord_431440, baseEnd_431440] using wordTrace_append hprefix tailTrace_431440
  have hstable : (prefixWord ++ tailWord_431440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431440).length < 2 ^ (prefixWord ++ tailWord_431440).sum := by decide
  have hdescent : baseEnd_431440 < baseStart_431440 := by decide
  rcases family_descends (prefixWord ++ tailWord_431440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431506 : List Nat := [3, 2, 3, 3, 2, 1, 1, 1, 1, 5]
def baseStart_431506 : Nat := 118140960795 + 431506 * 2 ^ 59
def prefixEnd_431506 : Nat := 4983230072969 + 3 ^ 40 * 431506 * 2
def baseEnd_431506 : Nat := 147713322199395976327031

theorem tailTrace_431506 : CollatzResearch.WordTrace tailWord_431506 prefixEnd_431506 147713322199395976327031 := by
  unfold tailWord_431506
  simp only [CollatzResearch.WordTrace]
  refine ⟨3934579193683733050680593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10492211183156621468481581 3934579193683733050680593)
  ·
    refine ⟨2950934395262799788010445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3934579193683733050680593 2950934395262799788010445)
    ·
      refine ⟨1106600398223549920503917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2950934395262799788010445 1106600398223549920503917)
      ·
        refine ⟨414975149333831220188969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1106600398223549920503917 414975149333831220188969)
        ·
          refine ⟨311231362000373415141727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 414975149333831220188969 311231362000373415141727)
          ·
            refine ⟨466847043000560122712591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311231362000373415141727 466847043000560122712591)
            ·
              refine ⟨700270564500840184068887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 466847043000560122712591 700270564500840184068887)
              ·
                refine ⟨1050405846751260276103331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 700270564500840184068887 1050405846751260276103331)
                ·
                  refine ⟨1575608770126890414154997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1050405846751260276103331 1575608770126890414154997)
                  ·
                    refine ⟨147713322199395976327031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1575608770126890414154997 147713322199395976327031)
                    ·
                      rfl

theorem cell22_431506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_431506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_431506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_431506 prefixEnd_431506 := by exact prefixLift 431506
  have htrace : WordTrace (prefixWord ++ tailWord_431506) baseStart_431506 baseEnd_431506 := by
    simpa [prefixWord, tailWord_431506, baseEnd_431506] using wordTrace_append hprefix tailTrace_431506
  have hstable : (prefixWord ++ tailWord_431506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431506).length < 2 ^ (prefixWord ++ tailWord_431506).sum := by decide
  have hdescent : baseEnd_431506 < baseStart_431506 := by decide
  rcases family_descends (prefixWord ++ tailWord_431506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431517 : List Nat := [1, 4, 2, 1, 3, 1, 2, 2, 3, 3]
def baseStart_431517 : Nat := 118140960795 + 431517 * 2 ^ 59
def prefixEnd_431517 : Nat := 4983230072969 + 3 ^ 40 * 431517 * 2
def baseEnd_431517 : Nat := 147717087724195614301997

theorem tailTrace_431517 : CollatzResearch.WordTrace tailWord_431517 prefixEnd_431517 147717087724195614301997 := by
  unfold tailWord_431517
  simp only [CollatzResearch.WordTrace]
  refine ⟨15738717977695081081372805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10492478651796720720915203 15738717977695081081372805)
  ·
    refine ⟨2951009620817827702757401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15738717977695081081372805 2951009620817827702757401)
    ·
      refine ⟨2213257215613370777068051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2951009620817827702757401 2213257215613370777068051)
      ·
        refine ⟨3319885823420056165602077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2213257215613370777068051 3319885823420056165602077)
        ·
          refine ⟨1244957183782521062100779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3319885823420056165602077 1244957183782521062100779)
          ·
            refine ⟨1867435775673781593151169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1244957183782521062100779 1867435775673781593151169)
            ·
              refine ⟨1400576831755336194863377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1867435775673781593151169 1400576831755336194863377)
              ·
                refine ⟨1050432623816502146147533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1400576831755336194863377 1050432623816502146147533)
                ·
                  refine ⟨393912233931188304805325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1050432623816502146147533 393912233931188304805325)
                  ·
                    refine ⟨147717087724195614301997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 393912233931188304805325 147717087724195614301997)
                    ·
                      rfl

theorem cell22_431517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_431517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_431517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_431517 prefixEnd_431517 := by exact prefixLift 431517
  have htrace : WordTrace (prefixWord ++ tailWord_431517) baseStart_431517 baseEnd_431517 := by
    simpa [prefixWord, tailWord_431517, baseEnd_431517] using wordTrace_append hprefix tailTrace_431517
  have hstable : (prefixWord ++ tailWord_431517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431517).length < 2 ^ (prefixWord ++ tailWord_431517).sum := by decide
  have hdescent : baseEnd_431517 < baseStart_431517 := by decide
  rcases family_descends (prefixWord ++ tailWord_431517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431560 : List Nat := [2, 1, 3, 1, 3, 1, 2, 2, 3, 4]
def baseStart_431560 : Nat := 118140960795 + 431560 * 2 ^ 59
def prefixEnd_431560 : Nat := 4983230072969 + 3 ^ 40 * 431560 * 2
def baseEnd_431560 : Nat := 147731807502957835476865

theorem tailTrace_431560 : CollatzResearch.WordTrace tailWord_431560 prefixEnd_431560 147731807502957835476865 := by
  unfold tailWord_431560
  simp only [CollatzResearch.WordTrace]
  refine ⟨7870143158269649712594067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10493524211026199616792089 7870143158269649712594067)
  ·
    refine ⟨11805214737404474568891101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7870143158269649712594067 11805214737404474568891101)
    ·
      refine ⟨4426955526526677963334163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11805214737404474568891101 4426955526526677963334163)
      ·
        refine ⟨6640433289790016945001245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4426955526526677963334163 6640433289790016945001245)
        ·
          refine ⟨2490162483671256354375467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6640433289790016945001245 2490162483671256354375467)
          ·
            refine ⟨3735243725506884531563201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2490162483671256354375467 3735243725506884531563201)
            ·
              refine ⟨2801432794130163398672401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3735243725506884531563201 2801432794130163398672401)
              ·
                refine ⟨2101074595597622549004301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2801432794130163398672401 2101074595597622549004301)
                ·
                  refine ⟨787902973349108455876613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2101074595597622549004301 787902973349108455876613)
                  ·
                    refine ⟨147731807502957835476865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 787902973349108455876613 147731807502957835476865)
                    ·
                      rfl

theorem cell22_431560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_431560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_431560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_431560 prefixEnd_431560 := by exact prefixLift 431560
  have htrace : WordTrace (prefixWord ++ tailWord_431560) baseStart_431560 baseEnd_431560 := by
    simpa [prefixWord, tailWord_431560, baseEnd_431560] using wordTrace_append hprefix tailTrace_431560
  have hstable : (prefixWord ++ tailWord_431560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431560).length < 2 ^ (prefixWord ++ tailWord_431560).sum := by decide
  have hdescent : baseEnd_431560 < baseStart_431560 := by decide
  rcases family_descends (prefixWord ++ tailWord_431560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431564 : List Nat := [2, 2, 1, 4, 2, 3, 2, 1, 5]
def baseStart_431564 : Nat := 118140960795 + 431564 * 2 ^ 59
def prefixEnd_431564 : Nat := 4983230072969 + 3 ^ 40 * 431564 * 2
def baseEnd_431564 : Nat := 49244392261567719458951

theorem tailTrace_431564 : CollatzResearch.WordTrace tailWord_431564 prefixEnd_431564 49244392261567719458951 := by
  unfold tailWord_431564
  simp only [CollatzResearch.WordTrace]
  refine ⟨7870216104262404054166873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10493621472349872072222497 7870216104262404054166873)
  ·
    refine ⟨5902662078196803040625155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7870216104262404054166873 5902662078196803040625155)
    ·
      refine ⟨8853993117295204560937733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5902662078196803040625155 8853993117295204560937733)
      ·
        refine ⟨1660123709492850855175825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8853993117295204560937733 1660123709492850855175825)
        ·
          refine ⟨1245092782119638141381869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1660123709492850855175825 1245092782119638141381869)
          ·
            refine ⟨466909793294864303018201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1245092782119638141381869 466909793294864303018201)
            ·
              refine ⟨350182344971148227263651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 466909793294864303018201 350182344971148227263651)
              ·
                refine ⟨525273517456722340895477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 350182344971148227263651 525273517456722340895477)
                ·
                  refine ⟨49244392261567719458951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 525273517456722340895477 49244392261567719458951)
                  ·
                    rfl

theorem cell22_431564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2, 1, 5].length) (baseStart_431564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_431564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_431564 prefixEnd_431564 := by exact prefixLift 431564
  have htrace : WordTrace (prefixWord ++ tailWord_431564) baseStart_431564 baseEnd_431564 := by
    simpa [prefixWord, tailWord_431564, baseEnd_431564] using wordTrace_append hprefix tailTrace_431564
  have hstable : (prefixWord ++ tailWord_431564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431564).length < 2 ^ (prefixWord ++ tailWord_431564).sum := by decide
  have hdescent : baseEnd_431564 < baseStart_431564 := by decide
  rcases family_descends (prefixWord ++ tailWord_431564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431577 : List Nat := [1, 2, 1, 2, 4, 2, 3, 2, 1, 4]
def baseStart_431577 : Nat := 118140960795 + 431577 * 2 ^ 59
def prefixEnd_431577 : Nat := 4983230072969 + 3 ^ 40 * 431577 * 2
def baseEnd_431577 : Nat := 147737626950375457801813

theorem tailTrace_431577 : CollatzResearch.WordTrace tailWord_431577 prefixEnd_431577 147737626950375457801813 := by
  unfold tailWord_431577
  simp only [CollatzResearch.WordTrace]
  refine ⟨15740906357477711328556985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10493937571651807552371323 15740906357477711328556985)
  ·
    refine ⟨11805679768108283496417739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15740906357477711328556985 11805679768108283496417739)
    ·
      refine ⟨17708519652162425244626609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11805679768108283496417739 17708519652162425244626609)
      ·
        refine ⟨13281389739121818933469957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17708519652162425244626609 13281389739121818933469957)
        ·
          refine ⟨2490260576085341050025617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13281389739121818933469957 2490260576085341050025617)
          ·
            refine ⟨1867695432064005787519213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2490260576085341050025617 1867695432064005787519213)
            ·
              refine ⟨700385787024002170319705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1867695432064005787519213 700385787024002170319705)
              ·
                refine ⟨525289340268001627739779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 700385787024002170319705 525289340268001627739779)
                ·
                  refine ⟨787934010402002441609669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 525289340268001627739779 787934010402002441609669)
                  ·
                    refine ⟨147737626950375457801813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 787934010402002441609669 147737626950375457801813)
                    ·
                      rfl

theorem cell22_431577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 2, 1, 4].length) (baseStart_431577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_431577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_431577 prefixEnd_431577 := by exact prefixLift 431577
  have htrace : WordTrace (prefixWord ++ tailWord_431577) baseStart_431577 baseEnd_431577 := by
    simpa [prefixWord, tailWord_431577, baseEnd_431577] using wordTrace_append hprefix tailTrace_431577
  have hstable : (prefixWord ++ tailWord_431577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431577).length < 2 ^ (prefixWord ++ tailWord_431577).sum := by decide
  have hdescent : baseEnd_431577 < baseStart_431577 := by decide
  rcases family_descends (prefixWord ++ tailWord_431577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431592 : List Nat := [2, 1, 4, 1, 1, 2, 2, 5, 4]
def baseStart_431592 : Nat := 118140960795 + 431592 * 2 ^ 59
def prefixEnd_431592 : Nat := 4983230072969 + 3 ^ 40 * 431592 * 2
def baseEnd_431592 : Nat := 49247587252306806225589

theorem tailTrace_431592 : CollatzResearch.WordTrace tailWord_431592 prefixEnd_431592 49247587252306806225589 := by
  unfold tailWord_431592
  simp only [CollatzResearch.WordTrace]
  refine ⟨7870726726211684445176515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10494302301615579260235353 7870726726211684445176515)
  ·
    refine ⟨11806090089317526667764773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7870726726211684445176515 11806090089317526667764773)
    ·
      refine ⟨2213641891747036250205895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11806090089317526667764773 2213641891747036250205895)
      ·
        refine ⟨3320462837620554375308843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2213641891747036250205895 3320462837620554375308843)
        ·
          refine ⟨4980694256430831562963265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3320462837620554375308843 4980694256430831562963265)
          ·
            refine ⟨3735520692323123672222449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4980694256430831562963265 3735520692323123672222449)
            ·
              refine ⟨2801640519242342754166837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3735520692323123672222449 2801640519242342754166837)
              ·
                refine ⟨262653798678969633203141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2801640519242342754166837 262653798678969633203141)
                ·
                  refine ⟨49247587252306806225589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 262653798678969633203141 49247587252306806225589)
                  ·
                    rfl

theorem cell22_431592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 5, 4].length) (baseStart_431592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_431592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_431592 prefixEnd_431592 := by exact prefixLift 431592
  have htrace : WordTrace (prefixWord ++ tailWord_431592) baseStart_431592 baseEnd_431592 := by
    simpa [prefixWord, tailWord_431592, baseEnd_431592] using wordTrace_append hprefix tailTrace_431592
  have hstable : (prefixWord ++ tailWord_431592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431592).length < 2 ^ (prefixWord ++ tailWord_431592).sum := by decide
  have hdescent : baseEnd_431592 < baseStart_431592 := by decide
  rcases family_descends (prefixWord ++ tailWord_431592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431637 : List Nat := [1, 3, 2, 1, 3, 3, 3, 6]
def baseStart_431637 : Nat := 118140960795 + 431637 * 2 ^ 59
def prefixEnd_431637 : Nat := 4983230072969 + 3 ^ 40 * 431637 * 2
def baseEnd_431637 : Nat := 16417574019617255700181

theorem tailTrace_431637 : CollatzResearch.WordTrace tailWord_431637 prefixEnd_431637 16417574019617255700181 := by
  unfold tailWord_431637
  simp only [CollatzResearch.WordTrace]
  refine ⟨15743094737260341575741165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10495396491506894383827443 15743094737260341575741165)
  ·
    refine ⟨5903660526472628090902937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15743094737260341575741165 5903660526472628090902937)
    ·
      refine ⟨4427745394854471068177203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5903660526472628090902937 4427745394854471068177203)
      ·
        refine ⟨6641618092281706602265805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4427745394854471068177203 6641618092281706602265805)
        ·
          refine ⟨2490606784605639975849677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6641618092281706602265805 2490606784605639975849677)
          ·
            refine ⟨933977544227114990943629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2490606784605639975849677 933977544227114990943629)
            ·
              refine ⟨350241579085168121603861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 933977544227114990943629 350241579085168121603861)
              ·
                refine ⟨16417574019617255700181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 350241579085168121603861 16417574019617255700181)
                ·
                  rfl

theorem cell22_431637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3, 6].length) (baseStart_431637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_431637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_431637 prefixEnd_431637 := by exact prefixLift 431637
  have htrace : WordTrace (prefixWord ++ tailWord_431637) baseStart_431637 baseEnd_431637 := by
    simpa [prefixWord, tailWord_431637, baseEnd_431637] using wordTrace_append hprefix tailTrace_431637
  have hstable : (prefixWord ++ tailWord_431637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431637).length < 2 ^ (prefixWord ++ tailWord_431637).sum := by decide
  have hdescent : baseEnd_431637 < baseStart_431637 := by decide
  rcases family_descends (prefixWord ++ tailWord_431637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431669 : List Nat := [1, 3, 3, 1, 1, 4, 2, 1, 3, 3]
def baseStart_431669 : Nat := 118140960795 + 431669 * 2 ^ 59
def prefixEnd_431669 : Nat := 4983230072969 + 3 ^ 40 * 431669 * 2
def baseEnd_431669 : Nat := 147769120430517884501531

theorem tailTrace_431669 : CollatzResearch.WordTrace tailWord_431669 prefixEnd_431669 147769120430517884501531 := by
  unfold tailWord_431669
  simp only [CollatzResearch.WordTrace]
  refine ⟨15744261873144411040906061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10496174582096274027270707 15744261873144411040906061)
  ·
    refine ⟨5904098202429154140339773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15744261873144411040906061 5904098202429154140339773)
    ·
      refine ⟨2214036825910932802627415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5904098202429154140339773 2214036825910932802627415)
      ·
        refine ⟨3321055238866399203941123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2214036825910932802627415 3321055238866399203941123)
        ·
          refine ⟨4981582858299598805911685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3321055238866399203941123 4981582858299598805911685)
          ·
            refine ⟨934046785931174776108441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4981582858299598805911685 934046785931174776108441)
            ·
              refine ⟨700535089448381082081331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 934046785931174776108441 700535089448381082081331)
              ·
                refine ⟨1050802634172571623121997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 700535089448381082081331 1050802634172571623121997)
                ·
                  refine ⟨394050987814714358670749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1050802634172571623121997 394050987814714358670749)
                  ·
                    refine ⟨147769120430517884501531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 394050987814714358670749 147769120430517884501531)
                    ·
                      rfl

theorem cell22_431669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_431669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_431669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_431669 prefixEnd_431669 := by exact prefixLift 431669
  have htrace : WordTrace (prefixWord ++ tailWord_431669) baseStart_431669 baseEnd_431669 := by
    simpa [prefixWord, tailWord_431669, baseEnd_431669] using wordTrace_append hprefix tailTrace_431669
  have hstable : (prefixWord ++ tailWord_431669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431669).length < 2 ^ (prefixWord ++ tailWord_431669).sum := by decide
  have hdescent : baseEnd_431669 < baseStart_431669 := by decide
  rcases family_descends (prefixWord ++ tailWord_431669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431755 : List Nat := [1, 1, 1, 1, 4, 1, 3, 10]
def baseStart_431755 : Nat := 118140960795 + 431755 * 2 ^ 59
def prefixEnd_431755 : Nat := 4983230072969 + 3 ^ 40 * 431755 * 2
def baseEnd_431755 : Nat := 16422062220893591872363

theorem tailTrace_431755 : CollatzResearch.WordTrace tailWord_431755 prefixEnd_431755 16422062220893591872363 := by
  unfold tailWord_431755
  simp only [CollatzResearch.WordTrace]
  refine ⟨15747398550832847728536719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10498265700555231819024479 15747398550832847728536719)
  ·
    refine ⟨23621097826249271592805079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15747398550832847728536719 23621097826249271592805079)
    ·
      refine ⟨35431646739373907389207619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23621097826249271592805079 35431646739373907389207619)
      ·
        refine ⟨53147470109060861083811429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35431646739373907389207619 53147470109060861083811429)
        ·
          refine ⟨9965150645448911453214643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53147470109060861083811429 9965150645448911453214643)
          ·
            refine ⟨14947725968173367179821965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9965150645448911453214643 14947725968173367179821965)
            ·
              refine ⟨5605397238065012692433237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14947725968173367179821965 5605397238065012692433237)
              ·
                refine ⟨16422062220893591872363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 5605397238065012692433237 16422062220893591872363)
                ·
                  rfl

theorem cell22_431755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 10].length) (baseStart_431755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_431755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_431755 prefixEnd_431755 := by exact prefixLift 431755
  have htrace : WordTrace (prefixWord ++ tailWord_431755) baseStart_431755 baseEnd_431755 := by
    simpa [prefixWord, tailWord_431755, baseEnd_431755] using wordTrace_append hprefix tailTrace_431755
  have hstable : (prefixWord ++ tailWord_431755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431755).length < 2 ^ (prefixWord ++ tailWord_431755).sum := by decide
  have hdescent : baseEnd_431755 < baseStart_431755 := by decide
  rcases family_descends (prefixWord ++ tailWord_431755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431772 : List Nat := [2, 2, 3, 2, 3, 10]
def baseStart_431772 : Nat := 118140960795 + 431772 * 2 ^ 59
def prefixEnd_431772 : Nat := 4983230072969 + 3 ^ 40 * 431772 * 2
def baseEnd_431772 : Nat := 1824745425129135175015

theorem tailTrace_431772 : CollatzResearch.WordTrace tailWord_431772 prefixEnd_431772 1824745425129135175015 := by
  unfold tailWord_431772
  simp only [CollatzResearch.WordTrace]
  refine ⟨7874009295885629815952785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10498679061180839754603713 7874009295885629815952785)
  ·
    refine ⟨5905506971914222361964589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7874009295885629815952785 5905506971914222361964589)
    ·
      refine ⟨2214565114467833385736721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5905506971914222361964589 2214565114467833385736721)
      ·
        refine ⟨1660923835850875039302541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2214565114467833385736721 1660923835850875039302541)
        ·
          refine ⟨622846438444078139738453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1660923835850875039302541 622846438444078139738453)
          ·
            refine ⟨1824745425129135175015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 622846438444078139738453 1824745425129135175015)
            ·
              rfl

theorem cell22_431772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 10].length) (baseStart_431772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_431772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_431772 prefixEnd_431772 := by exact prefixLift 431772
  have htrace : WordTrace (prefixWord ++ tailWord_431772) baseStart_431772 baseEnd_431772 := by
    simpa [prefixWord, tailWord_431772, baseEnd_431772] using wordTrace_append hprefix tailTrace_431772
  have hstable : (prefixWord ++ tailWord_431772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431772).length < 2 ^ (prefixWord ++ tailWord_431772).sum := by decide
  have hdescent : baseEnd_431772 < baseStart_431772 := by decide
  rcases family_descends (prefixWord ++ tailWord_431772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431776 : List Nat := [2, 1, 1, 4, 3, 2, 2, 2, 2, 3]
def baseStart_431776 : Nat := 118140960795 + 431776 * 2 ^ 59
def prefixEnd_431776 : Nat := 4983230072969 + 3 ^ 40 * 431776 * 2
def baseEnd_431776 : Nat := 147805748717205272076203

theorem tailTrace_431776 : CollatzResearch.WordTrace tailWord_431776 prefixEnd_431776 147805748717205272076203 := by
  unfold tailWord_431776
  simp only [CollatzResearch.WordTrace]
  refine ⟨7874082241878384157525591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10498776322504512210034121 7874082241878384157525591)
  ·
    refine ⟨11811123362817576236288387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7874082241878384157525591 11811123362817576236288387)
    ·
      refine ⟨17716685044226364354432581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11811123362817576236288387 17716685044226364354432581)
      ·
        refine ⟨3321878445792443316456109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17716685044226364354432581 3321878445792443316456109)
        ·
          refine ⟨1245704417172166243671041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3321878445792443316456109 1245704417172166243671041)
          ·
            refine ⟨934278312879124682753281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1245704417172166243671041 934278312879124682753281)
            ·
              refine ⟨700708734659343512064961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 934278312879124682753281 700708734659343512064961)
              ·
                refine ⟨525531550994507634048721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 700708734659343512064961 525531550994507634048721)
                ·
                  refine ⟨394148663245880725536541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 525531550994507634048721 394148663245880725536541)
                  ·
                    refine ⟨147805748717205272076203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 394148663245880725536541 147805748717205272076203)
                    ·
                      rfl

theorem cell22_431776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 2, 2, 3].length) (baseStart_431776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_431776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_431776 prefixEnd_431776 := by exact prefixLift 431776
  have htrace : WordTrace (prefixWord ++ tailWord_431776) baseStart_431776 baseEnd_431776 := by
    simpa [prefixWord, tailWord_431776, baseEnd_431776] using wordTrace_append hprefix tailTrace_431776
  have hstable : (prefixWord ++ tailWord_431776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431776).length < 2 ^ (prefixWord ++ tailWord_431776).sum := by decide
  have hdescent : baseEnd_431776 < baseStart_431776 := by decide
  rcases family_descends (prefixWord ++ tailWord_431776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431778 : List Nat := [3, 3, 1, 4, 1, 1, 1, 4, 4]
def baseStart_431778 : Nat := 118140960795 + 431778 * 2 ^ 59
def prefixEnd_431778 : Nat := 4983230072969 + 3 ^ 40 * 431778 * 2
def baseEnd_431778 : Nat := 49268811119359311175399

theorem tailTrace_431778 : CollatzResearch.WordTrace tailWord_431778 prefixEnd_431778 49268811119359311175399 := by
  unfold tailWord_431778
  simp only [CollatzResearch.WordTrace]
  refine ⟨3937059357437380664155997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10498824953166348437749325 3937059357437380664155997)
  ·
    refine ⟨1476397259039017749058499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3937059357437380664155997 1476397259039017749058499)
    ·
      refine ⟨2214595888558526623587749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1476397259039017749058499 2214595888558526623587749)
      ·
        refine ⟨415236729104723741922703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2214595888558526623587749 415236729104723741922703)
        ·
          refine ⟨622855093657085612884055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415236729104723741922703 622855093657085612884055)
          ·
            refine ⟨934282640485628419326083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 622855093657085612884055 934282640485628419326083)
            ·
              refine ⟨1401423960728442628989125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 934282640485628419326083 1401423960728442628989125)
              ·
                refine ⟨262766992636582992935461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1401423960728442628989125 262766992636582992935461)
                ·
                  refine ⟨49268811119359311175399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 262766992636582992935461 49268811119359311175399)
                  ·
                    rfl

theorem cell22_431778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_431778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_431778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_431778 prefixEnd_431778 := by exact prefixLift 431778
  have htrace : WordTrace (prefixWord ++ tailWord_431778) baseStart_431778 baseEnd_431778 := by
    simpa [prefixWord, tailWord_431778, baseEnd_431778] using wordTrace_append hprefix tailTrace_431778
  have hstable : (prefixWord ++ tailWord_431778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431778).length < 2 ^ (prefixWord ++ tailWord_431778).sum := by decide
  have hdescent : baseEnd_431778 < baseStart_431778 := by decide
  rcases family_descends (prefixWord ++ tailWord_431778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431804 : List Nat := [2, 2, 2, 3, 1, 2, 1, 1, 5, 3]
def baseStart_431804 : Nat := 118140960795 + 431804 * 2 ^ 59
def prefixEnd_431804 : Nat := 4983230072969 + 3 ^ 40 * 431804 * 2
def baseEnd_431804 : Nat := 147815333689422532376117

theorem tailTrace_431804 : CollatzResearch.WordTrace tailWord_431804 prefixEnd_431804 147815333689422532376117 := by
  unfold tailWord_431804
  simp only [CollatzResearch.WordTrace]
  refine ⟨7874592863827664548535233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10499457151770219398046977 7874592863827664548535233)
  ·
    refine ⟨5905944647870748411401425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7874592863827664548535233 5905944647870748411401425)
    ·
      refine ⟨4429458485903061308551069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5905944647870748411401425 4429458485903061308551069)
      ·
        refine ⟨1661046932213647990706651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4429458485903061308551069 1661046932213647990706651)
        ·
          refine ⟨2491570398320471986059977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1661046932213647990706651 2491570398320471986059977)
          ·
            refine ⟨1868677798740353989544983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2491570398320471986059977 1868677798740353989544983)
            ·
              refine ⟨2803016698110530984317475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1868677798740353989544983 2803016698110530984317475)
              ·
                refine ⟨4204525047165796476476213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2803016698110530984317475 4204525047165796476476213)
                ·
                  refine ⟨394174223171793419669645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4204525047165796476476213 394174223171793419669645)
                  ·
                    refine ⟨147815333689422532376117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 394174223171793419669645 147815333689422532376117)
                    ·
                      rfl

theorem cell22_431804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 5, 3].length) (baseStart_431804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_431804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_431804 prefixEnd_431804 := by exact prefixLift 431804
  have htrace : WordTrace (prefixWord ++ tailWord_431804) baseStart_431804 baseEnd_431804 := by
    simpa [prefixWord, tailWord_431804, baseEnd_431804] using wordTrace_append hprefix tailTrace_431804
  have hstable : (prefixWord ++ tailWord_431804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431804).length < 2 ^ (prefixWord ++ tailWord_431804).sum := by decide
  have hdescent : baseEnd_431804 < baseStart_431804 := by decide
  rcases family_descends (prefixWord ++ tailWord_431804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431832 : List Nat := [2, 1, 2, 2, 3, 1, 1, 1, 4, 5]
def baseStart_431832 : Nat := 118140960795 + 431832 * 2 ^ 59
def prefixEnd_431832 : Nat := 4983230072969 + 3 ^ 40 * 431832 * 2
def baseEnd_431832 : Nat := 147824918661639792676031

theorem tailTrace_431832 : CollatzResearch.WordTrace tailWord_431832 prefixEnd_431832 147824918661639792676031 := by
  unfold tailWord_431832
  simp only [CollatzResearch.WordTrace]
  refine ⟨7875103485776944939544875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10500137981035926586059833 7875103485776944939544875)
  ·
    refine ⟨11812655228665417409317313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7875103485776944939544875 11812655228665417409317313)
    ·
      refine ⟨8859491421499063056987985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11812655228665417409317313 8859491421499063056987985)
      ·
        refine ⟨6644618566124297292740989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8859491421499063056987985 6644618566124297292740989)
        ·
          refine ⟨2491731962296611484777871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6644618566124297292740989 2491731962296611484777871)
          ·
            refine ⟨3737597943444917227166807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2491731962296611484777871 3737597943444917227166807)
            ·
              refine ⟨5606396915167375840750211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3737597943444917227166807 5606396915167375840750211)
              ·
                refine ⟨8409595372751063761125317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5606396915167375840750211 8409595372751063761125317)
                ·
                  refine ⟨1576799132390824455210997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8409595372751063761125317 1576799132390824455210997)
                  ·
                    refine ⟨147824918661639792676031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1576799132390824455210997 147824918661639792676031)
                    ·
                      rfl

theorem cell22_431832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 4, 5].length) (baseStart_431832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_431832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_431832 prefixEnd_431832 := by exact prefixLift 431832
  have htrace : WordTrace (prefixWord ++ tailWord_431832) baseStart_431832 baseEnd_431832 := by
    simpa [prefixWord, tailWord_431832, baseEnd_431832] using wordTrace_append hprefix tailTrace_431832
  have hstable : (prefixWord ++ tailWord_431832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431832).length < 2 ^ (prefixWord ++ tailWord_431832).sum := by decide
  have hdescent : baseEnd_431832 < baseStart_431832 := by decide
  rcases family_descends (prefixWord ++ tailWord_431832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431834 : List Nat := [3, 1, 1, 2, 2, 3, 3, 2, 5]
def baseStart_431834 : Nat := 118140960795 + 431834 * 2 ^ 59
def prefixEnd_431834 : Nat := 4983230072969 + 3 ^ 40 * 431834 * 2
def baseEnd_431834 : Nat := 49275201100837484708675

theorem tailTrace_431834 : CollatzResearch.WordTrace tailWord_431834 prefixEnd_431834 49275201100837484708675 := by
  unfold tailWord_431834
  simp only [CollatzResearch.WordTrace]
  refine ⟨3937569979386661055165639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10500186611697762813775037 3937569979386661055165639)
  ·
    refine ⟨5906354969079991582748459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3937569979386661055165639 5906354969079991582748459)
    ·
      refine ⟨8859532453619987374122689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5906354969079991582748459 8859532453619987374122689)
      ·
        refine ⟨6644649340214990530592017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8859532453619987374122689 6644649340214990530592017)
        ·
          refine ⟨4983487005161242897944013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6644649340214990530592017 4983487005161242897944013)
          ·
            refine ⟨1868807626935466086729005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4983487005161242897944013 1868807626935466086729005)
            ·
              refine ⟨700802860100799782523377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1868807626935466086729005 700802860100799782523377)
              ·
                refine ⟨525602145075599836892533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 700802860100799782523377 525602145075599836892533)
                ·
                  refine ⟨49275201100837484708675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 525602145075599836892533 49275201100837484708675)
                  ·
                    rfl

theorem cell22_431834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 2, 5].length) (baseStart_431834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_431834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_431834 prefixEnd_431834 := by exact prefixLift 431834
  have htrace : WordTrace (prefixWord ++ tailWord_431834) baseStart_431834 baseEnd_431834 := by
    simpa [prefixWord, tailWord_431834, baseEnd_431834] using wordTrace_append hprefix tailTrace_431834
  have hstable : (prefixWord ++ tailWord_431834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431834).length < 2 ^ (prefixWord ++ tailWord_431834).sum := by decide
  have hdescent : baseEnd_431834 < baseStart_431834 := by decide
  rcases family_descends (prefixWord ++ tailWord_431834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431902 : List Nat := [4, 3, 2, 2, 1, 2, 2, 1, 5]
def baseStart_431902 : Nat := 118140960795 + 431902 * 2 ^ 59
def prefixEnd_431902 : Nat := 4983230072969 + 3 ^ 40 * 431902 * 2
def baseEnd_431902 : Nat := 49282960364060981141939

theorem tailTrace_431902 : CollatzResearch.WordTrace tailWord_431902 prefixEnd_431902 49282960364060981141939 := by
  unfold tailWord_431902
  simp only [CollatzResearch.WordTrace]
  refine ⟨1969095010162536479267245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10501840054200194556091973 1969095010162536479267245)
  ·
    refine ⟨738410628810951179725217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1969095010162536479267245 738410628810951179725217)
    ·
      refine ⟨553807971608213384793913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 738410628810951179725217 553807971608213384793913)
      ·
        refine ⟨415355978706160038595435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 553807971608213384793913 415355978706160038595435)
        ·
          refine ⟨623033968059240057893153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415355978706160038595435 623033968059240057893153)
          ·
            refine ⟨467275476044430043419865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 623033968059240057893153 467275476044430043419865)
            ·
              refine ⟨350456607033322532564899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 467275476044430043419865 350456607033322532564899)
              ·
                refine ⟨525684910549983798847349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 350456607033322532564899 525684910549983798847349)
                ·
                  refine ⟨49282960364060981141939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 525684910549983798847349 49282960364060981141939)
                  ·
                    rfl

theorem cell22_431902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_431902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_431902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_431902 prefixEnd_431902 := by exact prefixLift 431902
  have htrace : WordTrace (prefixWord ++ tailWord_431902) baseStart_431902 baseEnd_431902 := by
    simpa [prefixWord, tailWord_431902, baseEnd_431902] using wordTrace_append hprefix tailTrace_431902
  have hstable : (prefixWord ++ tailWord_431902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431902).length < 2 ^ (prefixWord ++ tailWord_431902).sum := by decide
  have hdescent : baseEnd_431902 < baseStart_431902 := by decide
  rcases family_descends (prefixWord ++ tailWord_431902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431907 : List Nat := [1, 1, 1, 4, 2, 1, 3, 9]
def baseStart_431907 : Nat := 118140960795 + 431907 * 2 ^ 59
def prefixEnd_431907 : Nat := 4983230072969 + 3 ^ 40 * 431907 * 2
def baseEnd_431907 : Nat := 16427843632707177450089

theorem tailTrace_431907 : CollatzResearch.WordTrace tailWord_431907 prefixEnd_431907 16427843632707177450089 := by
  unfold tailWord_431907
  simp only [CollatzResearch.WordTrace]
  refine ⟨15752942446282177688069975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10501961630854785125379983 15752942446282177688069975)
  ·
    refine ⟨23629413669423266532104963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15752942446282177688069975 23629413669423266532104963)
    ·
      refine ⟨35444120504134899798157445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23629413669423266532104963 35444120504134899798157445)
      ·
        refine ⟨6645772594525293712154521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35444120504134899798157445 6645772594525293712154521)
        ·
          refine ⟨4984329445893970284115891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6645772594525293712154521 4984329445893970284115891)
          ·
            refine ⟨7476494168840955426173837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4984329445893970284115891 7476494168840955426173837)
            ·
              refine ⟨2803685313315358284815189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7476494168840955426173837 2803685313315358284815189)
              ·
                refine ⟨16427843632707177450089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2803685313315358284815189 16427843632707177450089)
                ·
                  rfl

theorem cell22_431907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 9].length) (baseStart_431907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_431907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_431907 prefixEnd_431907 := by exact prefixLift 431907
  have htrace : WordTrace (prefixWord ++ tailWord_431907) baseStart_431907 baseEnd_431907 := by
    simpa [prefixWord, tailWord_431907, baseEnd_431907] using wordTrace_append hprefix tailTrace_431907
  have hstable : (prefixWord ++ tailWord_431907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431907).length < 2 ^ (prefixWord ++ tailWord_431907).sum := by decide
  have hdescent : baseEnd_431907 < baseStart_431907 := by decide
  rcases family_descends (prefixWord ++ tailWord_431907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431954 : List Nat := [3, 2, 2, 1, 1, 3, 1, 1, 2, 6]
def baseStart_431954 : Nat := 118140960795 + 431954 * 2 ^ 59
def prefixEnd_431954 : Nat := 4983230072969 + 3 ^ 40 * 431954 * 2
def baseEnd_431954 : Nat := 147866681754872141125657

theorem tailTrace_431954 : CollatzResearch.WordTrace tailWord_431954 prefixEnd_431954 147866681754872141125657 := by
  unfold tailWord_431954
  simp only [CollatzResearch.WordTrace]
  refine ⟨3938664169277976178757729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10503104451407936476687277 3938664169277976178757729)
  ·
    refine ⟨2953998126958482134068297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3938664169277976178757729 2953998126958482134068297)
    ·
      refine ⟨2215498595218861600551223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2953998126958482134068297 2215498595218861600551223)
      ·
        refine ⟨3323247892828292400826835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2215498595218861600551223 3323247892828292400826835)
        ·
          refine ⟨4984871839242438601240253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3323247892828292400826835 4984871839242438601240253)
          ·
            refine ⟨1869326939715914475465095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4984871839242438601240253 1869326939715914475465095)
            ·
              refine ⟨2803990409573871713197643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1869326939715914475465095 2803990409573871713197643)
              ·
                refine ⟨4205985614360807569796465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2803990409573871713197643 4205985614360807569796465)
                ·
                  refine ⟨3154489210770605677347349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4205985614360807569796465 3154489210770605677347349)
                  ·
                    refine ⟨147866681754872141125657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3154489210770605677347349 147866681754872141125657)
                    ·
                      rfl

theorem cell22_431954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_431954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_431954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_431954 prefixEnd_431954 := by exact prefixLift 431954
  have htrace : WordTrace (prefixWord ++ tailWord_431954) baseStart_431954 baseEnd_431954 := by
    simpa [prefixWord, tailWord_431954, baseEnd_431954] using wordTrace_append hprefix tailTrace_431954
  have hstable : (prefixWord ++ tailWord_431954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431954).length < 2 ^ (prefixWord ++ tailWord_431954).sum := by decide
  have hdescent : baseEnd_431954 < baseStart_431954 := by decide
  rcases family_descends (prefixWord ++ tailWord_431954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431969 : List Nat := [1, 2, 3, 1, 1, 1, 3, 5, 5]
def baseStart_431969 : Nat := 118140960795 + 431969 * 2 ^ 59
def prefixEnd_431969 : Nat := 4983230072969 + 3 ^ 40 * 431969 * 2
def baseEnd_431969 : Nat := 49290605520472367333537

theorem tailTrace_431969 : CollatzResearch.WordTrace tailWord_431969 prefixEnd_431969 49290605520472367333537 := by
  unfold tailWord_431969
  simp only [CollatzResearch.WordTrace]
  refine ⟨15755203772057562276826961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10503469181371708184551307 15755203772057562276826961)
  ·
    refine ⟨11816402829043171707620221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15755203772057562276826961 11816402829043171707620221)
    ·
      refine ⟨4431151060891189390357583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11816402829043171707620221 4431151060891189390357583)
      ·
        refine ⟨6646726591336784085536375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4431151060891189390357583 6646726591336784085536375)
        ·
          refine ⟨9970089887005176128304563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6646726591336784085536375 9970089887005176128304563)
          ·
            refine ⟨14955134830507764192456845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9970089887005176128304563 14955134830507764192456845)
            ·
              refine ⟨5608175561440411572171317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14955134830507764192456845 5608175561440411572171317)
              ·
                refine ⟨525766458885038584891061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5608175561440411572171317 525766458885038584891061)
                ·
                  refine ⟨49290605520472367333537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 525766458885038584891061 49290605520472367333537)
                  ·
                    rfl

theorem cell22_431969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 5, 5].length) (baseStart_431969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_431969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_431969 prefixEnd_431969 := by exact prefixLift 431969
  have htrace : WordTrace (prefixWord ++ tailWord_431969) baseStart_431969 baseEnd_431969 := by
    simpa [prefixWord, tailWord_431969, baseEnd_431969] using wordTrace_append hprefix tailTrace_431969
  have hstable : (prefixWord ++ tailWord_431969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431969).length < 2 ^ (prefixWord ++ tailWord_431969).sum := by decide
  have hdescent : baseEnd_431969 < baseStart_431969 := by decide
  rcases family_descends (prefixWord ++ tailWord_431969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432061 : List Nat := [1, 4, 1, 2, 3, 1, 1, 1, 4, 4]
def baseStart_432061 : Nat := 118140960795 + 432061 * 2 ^ 59
def prefixEnd_432061 : Nat := 4983230072969 + 3 ^ 40 * 432061 * 2
def baseEnd_432061 : Nat := 147903310041559528700329

theorem tailTrace_432061 : CollatzResearch.WordTrace tailWord_432061 prefixEnd_432061 147903310041559528700329 := by
  unfold tailWord_432061
  simp only [CollatzResearch.WordTrace]
  refine ⟨15758559287724261989176037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10505706191816174659450691 15758559287724261989176037)
  ·
    refine ⟨2954729866448299122970507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15758559287724261989176037 2954729866448299122970507)
    ·
      refine ⟨4432094799672448684455761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2954729866448299122970507 4432094799672448684455761)
      ·
        refine ⟨3324071099754336513341821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4432094799672448684455761 3324071099754336513341821)
        ·
          refine ⟨1246526662407876192503183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3324071099754336513341821 1246526662407876192503183)
          ·
            refine ⟨1869789993611814288754775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1246526662407876192503183 1869789993611814288754775)
            ·
              refine ⟨2804684990417721433132163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1869789993611814288754775 2804684990417721433132163)
              ·
                refine ⟨4207027485626582149698245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2804684990417721433132163 4207027485626582149698245)
                ·
                  refine ⟨788817653554984153068421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4207027485626582149698245 788817653554984153068421)
                  ·
                    refine ⟨147903310041559528700329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 788817653554984153068421 147903310041559528700329)
                    ·
                      rfl

theorem cell22_432061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_432061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_432061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_432061 prefixEnd_432061 := by exact prefixLift 432061
  have htrace : WordTrace (prefixWord ++ tailWord_432061) baseStart_432061 baseEnd_432061 := by
    simpa [prefixWord, tailWord_432061, baseEnd_432061] using wordTrace_append hprefix tailTrace_432061
  have hstable : (prefixWord ++ tailWord_432061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432061).length < 2 ^ (prefixWord ++ tailWord_432061).sum := by decide
  have hdescent : baseEnd_432061 < baseStart_432061 := by decide
  rcases family_descends (prefixWord ++ tailWord_432061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432076 : List Nat := [2, 2, 1, 4, 1, 3, 2, 7]
def baseStart_432076 : Nat := 118140960795 + 432076 * 2 ^ 59
def prefixEnd_432076 : Nat := 4983230072969 + 3 ^ 40 * 432076 * 2
def baseEnd_432076 : Nat := 16434271649789387730587

theorem tailTrace_432076 : CollatzResearch.WordTrace tailWord_432076 prefixEnd_432076 16434271649789387730587 := by
  unfold tailWord_432076
  simp only [CollatzResearch.WordTrace]
  refine ⟨7879553191334959775486041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10506070921779946367314721 7879553191334959775486041)
  ·
    refine ⟨5909664893501219831614531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7879553191334959775486041 5909664893501219831614531)
    ·
      refine ⟨8864497340251829747421797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5909664893501219831614531 8864497340251829747421797)
      ·
        refine ⟨1662093251297218077641587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8864497340251829747421797 1662093251297218077641587)
        ·
          refine ⟨2493139876945827116462381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1662093251297218077641587 2493139876945827116462381)
          ·
            refine ⟨934927453854685168673393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2493139876945827116462381 934927453854685168673393)
            ·
              refine ⟨701195590391013876505045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 934927453854685168673393 701195590391013876505045)
              ·
                refine ⟨16434271649789387730587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 701195590391013876505045 16434271649789387730587)
                ·
                  rfl

theorem cell22_432076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 7].length) (baseStart_432076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_432076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_432076 prefixEnd_432076 := by exact prefixLift 432076
  have htrace : WordTrace (prefixWord ++ tailWord_432076) baseStart_432076 baseEnd_432076 := by
    simpa [prefixWord, tailWord_432076, baseEnd_432076] using wordTrace_append hprefix tailTrace_432076
  have hstable : (prefixWord ++ tailWord_432076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432076).length < 2 ^ (prefixWord ++ tailWord_432076).sum := by decide
  have hdescent : baseEnd_432076 < baseStart_432076 := by decide
  rcases family_descends (prefixWord ++ tailWord_432076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432119 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 5, 7]
def baseStart_432119 : Nat := 118140960795 + 432119 * 2 ^ 59
def prefixEnd_432119 : Nat := 4983230072969 + 3 ^ 40 * 432119 * 2
def baseEnd_432119 : Nat := 147923164626866710750151

theorem tailTrace_432119 : CollatzResearch.WordTrace tailWord_432119 prefixEnd_432119 147923164626866710750151 := by
  unfold tailWord_432119
  simp only [CollatzResearch.WordTrace]
  refine ⟨15760674721514137894787411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10507116481009425263191607 15760674721514137894787411)
  ·
    refine ⟨23641012082271206842181117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15760674721514137894787411 23641012082271206842181117)
    ·
      refine ⟨8865379530851702565817919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23641012082271206842181117 8865379530851702565817919)
      ·
        refine ⟨13298069296277553848726879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8865379530851702565817919 13298069296277553848726879)
        ·
          refine ⟨19947103944416330773090319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13298069296277553848726879 19947103944416330773090319)
          ·
            refine ⟨29920655916624496159635479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19947103944416330773090319 29920655916624496159635479)
            ·
              refine ⟨44880983874936744239453219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29920655916624496159635479 44880983874936744239453219)
              ·
                refine ⟨67321475812405116359179829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44880983874936744239453219 67321475812405116359179829)
                ·
                  refine ⟨6311388357412979658673109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67321475812405116359179829 6311388357412979658673109)
                  ·
                    refine ⟨147923164626866710750151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6311388357412979658673109 147923164626866710750151)
                    ·
                      rfl

theorem cell22_432119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 7].length) (baseStart_432119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_432119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_432119 prefixEnd_432119 := by exact prefixLift 432119
  have htrace : WordTrace (prefixWord ++ tailWord_432119) baseStart_432119 baseEnd_432119 := by
    simpa [prefixWord, tailWord_432119, baseEnd_432119] using wordTrace_append hprefix tailTrace_432119
  have hstable : (prefixWord ++ tailWord_432119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432119).length < 2 ^ (prefixWord ++ tailWord_432119).sum := by decide
  have hdescent : baseEnd_432119 < baseStart_432119 := by decide
  rcases family_descends (prefixWord ++ tailWord_432119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432121 : List Nat := [1, 2, 1, 3, 1, 4, 1, 4, 5]
def baseStart_432121 : Nat := 118140960795 + 432121 * 2 ^ 59
def prefixEnd_432121 : Nat := 4983230072969 + 3 ^ 40 * 432121 * 2
def baseEnd_432121 : Nat := 49307949755913124066715

theorem tailTrace_432121 : CollatzResearch.WordTrace tailWord_432121 prefixEnd_432121 49307949755913124066715 := by
  unfold tailWord_432121
  simp only [CollatzResearch.WordTrace]
  refine ⟨15760747667506892236360217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10507165111671261490906811 15760747667506892236360217)
  ·
    refine ⟨11820560750630169177270163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15760747667506892236360217 11820560750630169177270163)
    ·
      refine ⟨17730841125945253765905245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11820560750630169177270163 17730841125945253765905245)
      ·
        refine ⟨6649065422229470162214467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17730841125945253765905245 6649065422229470162214467)
        ·
          refine ⟨9973598133344205243321701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6649065422229470162214467 9973598133344205243321701)
          ·
            refine ⟨1870049650002038483122819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9973598133344205243321701 1870049650002038483122819)
            ·
              refine ⟨2805074475003057724684229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1870049650002038483122819 2805074475003057724684229)
              ·
                refine ⟨525951464063073323378293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2805074475003057724684229 525951464063073323378293)
                ·
                  refine ⟨49307949755913124066715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 525951464063073323378293 49307949755913124066715)
                  ·
                    rfl

theorem cell22_432121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 4, 5].length) (baseStart_432121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_432121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_432121 prefixEnd_432121 := by exact prefixLift 432121
  have htrace : WordTrace (prefixWord ++ tailWord_432121) baseStart_432121 baseEnd_432121 := by
    simpa [prefixWord, tailWord_432121, baseEnd_432121] using wordTrace_append hprefix tailTrace_432121
  have hstable : (prefixWord ++ tailWord_432121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432121).length < 2 ^ (prefixWord ++ tailWord_432121).sum := by decide
  have hdescent : baseEnd_432121 < baseStart_432121 := by decide
  rcases family_descends (prefixWord ++ tailWord_432121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432136 : List Nat := [2, 1, 3, 2, 1, 2, 3, 1, 2, 5]
def baseStart_432136 : Nat := 118140960795 + 432136 * 2 ^ 59
def prefixEnd_432136 : Nat := 4983230072969 + 3 ^ 40 * 432136 * 2
def baseEnd_432136 : Nat := 147928984074284333075099

theorem tailTrace_432136 : CollatzResearch.WordTrace tailWord_432136 prefixEnd_432136 147928984074284333075099 := by
  unfold tailWord_432136
  simp only [CollatzResearch.WordTrace]
  refine ⟨7880647381226274899078131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10507529841635033198770841 7880647381226274899078131)
  ·
    refine ⟨11820971071839412348617197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7880647381226274899078131 11820971071839412348617197)
    ·
      refine ⟨4432864151939779630731449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11820971071839412348617197 4432864151939779630731449)
      ·
        refine ⟨3324648113954834723048587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4432864151939779630731449 3324648113954834723048587)
        ·
          refine ⟨4986972170932252084572881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3324648113954834723048587 4986972170932252084572881)
          ·
            refine ⟨3740229128199189063429661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4986972170932252084572881 3740229128199189063429661)
            ·
              refine ⟨1402585923074695898786123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3740229128199189063429661 1402585923074695898786123)
              ·
                refine ⟨2103878884612043848179185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1402585923074695898786123 2103878884612043848179185)
                ·
                  refine ⟨1577909163459032886134389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2103878884612043848179185 1577909163459032886134389)
                  ·
                    refine ⟨147928984074284333075099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1577909163459032886134389 147928984074284333075099)
                    ·
                      rfl

theorem cell22_432136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_432136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_432136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_432136 prefixEnd_432136 := by exact prefixLift 432136
  have htrace : WordTrace (prefixWord ++ tailWord_432136) baseStart_432136 baseEnd_432136 := by
    simpa [prefixWord, tailWord_432136, baseEnd_432136] using wordTrace_append hprefix tailTrace_432136
  have hstable : (prefixWord ++ tailWord_432136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432136).length < 2 ^ (prefixWord ++ tailWord_432136).sum := by decide
  have hdescent : baseEnd_432136 < baseStart_432136 := by decide
  rcases family_descends (prefixWord ++ tailWord_432136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432181 : List Nat := [1, 3, 3, 1, 1, 1, 2, 2, 3, 5]
def baseStart_432181 : Nat := 118140960795 + 432181 * 2 ^ 59
def prefixEnd_432181 : Nat := 4983230072969 + 3 ^ 40 * 432181 * 2
def baseEnd_432181 : Nat := 147944388493919215699961

theorem tailTrace_432181 : CollatzResearch.WordTrace tailWord_432181 prefixEnd_432181 147944388493919215699961 := by
  unfold tailWord_432181
  simp only [CollatzResearch.WordTrace]
  refine ⟨15762936047289522483544397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10508624031526348322362931 15762936047289522483544397)
  ·
    refine ⟨5911101017733570931329149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15762936047289522483544397 5911101017733570931329149)
    ·
      refine ⟨2216662881650089099248431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5911101017733570931329149 2216662881650089099248431)
      ·
        refine ⟨3324994322475133648872647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2216662881650089099248431 3324994322475133648872647)
        ·
          refine ⟨4987491483712700473308971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3324994322475133648872647 4987491483712700473308971)
          ·
            refine ⟨7481237225569050709963457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4987491483712700473308971 7481237225569050709963457)
            ·
              refine ⟨5610927919176788032472593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7481237225569050709963457 5610927919176788032472593)
              ·
                refine ⟨4208195939382591024354445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5610927919176788032472593 4208195939382591024354445)
                ·
                  refine ⟨1578073477268471634132917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4208195939382591024354445 1578073477268471634132917)
                  ·
                    refine ⟨147944388493919215699961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1578073477268471634132917 147944388493919215699961)
                    ·
                      rfl

theorem cell22_432181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_432181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_432181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_432181 prefixEnd_432181 := by exact prefixLift 432181
  have htrace : WordTrace (prefixWord ++ tailWord_432181) baseStart_432181 baseEnd_432181 := by
    simpa [prefixWord, tailWord_432181, baseEnd_432181] using wordTrace_append hprefix tailTrace_432181
  have hstable : (prefixWord ++ tailWord_432181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432181).length < 2 ^ (prefixWord ++ tailWord_432181).sum := by decide
  have hdescent : baseEnd_432181 < baseStart_432181 := by decide
  rcases family_descends (prefixWord ++ tailWord_432181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432183 : List Nat := [1, 1, 3, 1, 2, 2, 4, 4, 4]
def baseStart_432183 : Nat := 118140960795 + 432183 * 2 ^ 59
def prefixEnd_432183 : Nat := 4983230072969 + 3 ^ 40 * 432183 * 2
def baseEnd_432183 : Nat := 49315024378263959049985

theorem tailTrace_432183 : CollatzResearch.WordTrace tailWord_432183 prefixEnd_432183 49315024378263959049985 := by
  unfold tailWord_432183
  simp only [CollatzResearch.WordTrace]
  refine ⟨15763008993282276825117203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10508672662188184550078135 15763008993282276825117203)
  ·
    refine ⟨23644513489923415237675805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15763008993282276825117203 23644513489923415237675805)
    ·
      refine ⟨8866692558721280714128427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23644513489923415237675805 8866692558721280714128427)
      ·
        refine ⟨13300038838081921071192641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8866692558721280714128427 13300038838081921071192641)
        ·
          refine ⟨9975029128561440803394481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13300038838081921071192641 9975029128561440803394481)
          ·
            refine ⟨7481271846421080602545861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9975029128561440803394481 7481271846421080602545861)
            ·
              refine ⟨1402738471203952612977349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7481271846421080602545861 1402738471203952612977349)
              ·
                refine ⟨263013463350741114933253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1402738471203952612977349 263013463350741114933253)
                ·
                  refine ⟨49315024378263959049985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 263013463350741114933253 49315024378263959049985)
                  ·
                    rfl

theorem cell22_432183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 4, 4].length) (baseStart_432183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_432183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_432183 prefixEnd_432183 := by exact prefixLift 432183
  have htrace : WordTrace (prefixWord ++ tailWord_432183) baseStart_432183 baseEnd_432183 := by
    simpa [prefixWord, tailWord_432183, baseEnd_432183] using wordTrace_append hprefix tailTrace_432183
  have hstable : (prefixWord ++ tailWord_432183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432183).length < 2 ^ (prefixWord ++ tailWord_432183).sum := by decide
  have hdescent : baseEnd_432183 < baseStart_432183 := by decide
  rcases family_descends (prefixWord ++ tailWord_432183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432241 : List Nat := [1, 2, 2, 2, 1, 1, 4, 1, 2, 6]
def baseStart_432241 : Nat := 118140960795 + 432241 * 2 ^ 59
def prefixEnd_432241 : Nat := 4983230072969 + 3 ^ 40 * 432241 * 2
def baseEnd_432241 : Nat := 147964927720099059199777

theorem tailTrace_432241 : CollatzResearch.WordTrace tailWord_432241 prefixEnd_432241 147964927720099059199777 := by
  unfold tailWord_432241
  simp only [CollatzResearch.WordTrace]
  refine ⟨15765124427072152730728577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10510082951381435153819051 15765124427072152730728577)
  ·
    refine ⟨11823843320304114548046433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15765124427072152730728577 11823843320304114548046433)
    ·
      refine ⟨8867882490228085911034825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11823843320304114548046433 8867882490228085911034825)
      ·
        refine ⟨6650911867671064433276119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8867882490228085911034825 6650911867671064433276119)
        ·
          refine ⟨9976367801506596649914179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6650911867671064433276119 9976367801506596649914179)
          ·
            refine ⟨14964551702259894974871269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9976367801506596649914179 14964551702259894974871269)
            ·
              refine ⟨2805853444173730307788363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14964551702259894974871269 2805853444173730307788363)
              ·
                refine ⟨4208780166260595461682545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2805853444173730307788363 4208780166260595461682545)
                ·
                  refine ⟨3156585124695446596261909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4208780166260595461682545 3156585124695446596261909)
                  ·
                    refine ⟨147964927720099059199777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3156585124695446596261909 147964927720099059199777)
                    ·
                      rfl

theorem cell22_432241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 6].length) (baseStart_432241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_432241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_432241 prefixEnd_432241 := by exact prefixLift 432241
  have htrace : WordTrace (prefixWord ++ tailWord_432241) baseStart_432241 baseEnd_432241 := by
    simpa [prefixWord, tailWord_432241, baseEnd_432241] using wordTrace_append hprefix tailTrace_432241
  have hstable : (prefixWord ++ tailWord_432241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432241).length < 2 ^ (prefixWord ++ tailWord_432241).sum := by decide
  have hdescent : baseEnd_432241 < baseStart_432241 := by decide
  rcases family_descends (prefixWord ++ tailWord_432241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432290 : List Nat := [3, 3, 1, 3, 1, 1, 1, 4, 5]
def baseStart_432290 : Nat := 118140960795 + 432290 * 2 ^ 59
def prefixEnd_432290 : Nat := 4983230072969 + 3 ^ 40 * 432290 * 2
def baseEnd_432290 : Nat := 49327233807159754908209

theorem tailTrace_432290 : CollatzResearch.WordTrace tailWord_432290 prefixEnd_432290 49327233807159754908209 := by
  unfold tailWord_432290
  simp only [CollatzResearch.WordTrace]
  refine ⟨3941727900973658524815581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10511274402596422732841549 3941727900973658524815581)
  ·
    refine ⟨1478147962865121946805843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3941727900973658524815581 1478147962865121946805843)
    ·
      refine ⟨2217221944297682920208765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1478147962865121946805843 2217221944297682920208765)
      ·
        refine ⟨831458229111631095078287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2217221944297682920208765 831458229111631095078287)
        ·
          refine ⟨1247187343667446642617431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 831458229111631095078287 1247187343667446642617431)
          ·
            refine ⟨1870781015501169963926147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1247187343667446642617431 1870781015501169963926147)
            ·
              refine ⟨2806171523251754945889221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1870781015501169963926147 2806171523251754945889221)
              ·
                refine ⟨526157160609704052354229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2806171523251754945889221 526157160609704052354229)
                ·
                  refine ⟨49327233807159754908209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 526157160609704052354229 49327233807159754908209)
                  ·
                    rfl

theorem cell22_432290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_432290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_432290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_432290 prefixEnd_432290 := by exact prefixLift 432290
  have htrace : WordTrace (prefixWord ++ tailWord_432290) baseStart_432290 baseEnd_432290 := by
    simpa [prefixWord, tailWord_432290, baseEnd_432290] using wordTrace_append hprefix tailTrace_432290
  have hstable : (prefixWord ++ tailWord_432290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432290).length < 2 ^ (prefixWord ++ tailWord_432290).sum := by decide
  have hdescent : baseEnd_432290 < baseStart_432290 := by decide
  rcases family_descends (prefixWord ++ tailWord_432290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432305 : List Nat := [1, 2, 2, 5, 2, 1, 1, 1, 2, 5]
def baseStart_432305 : Nat := 118140960795 + 432305 * 2 ^ 59
def prefixEnd_432305 : Nat := 4983230072969 + 3 ^ 40 * 432305 * 2
def baseEnd_432305 : Nat := 147986836228024225599581

theorem tailTrace_432305 : CollatzResearch.WordTrace tailWord_432305 prefixEnd_432305 147986836228024225599581 := by
  unfold tailWord_432305
  simp only [CollatzResearch.WordTrace]
  refine ⟨15767458698840291661058369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10511639132560194440705579 15767458698840291661058369)
  ·
    refine ⟨11825594024130218745793777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15767458698840291661058369 11825594024130218745793777)
    ·
      refine ⟨8869195518097664059345333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11825594024130218745793777 8869195518097664059345333)
      ·
        refine ⟨831487079821656005563625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8869195518097664059345333 831487079821656005563625)
        ·
          refine ⟨623615309866242004172719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 831487079821656005563625 623615309866242004172719)
          ·
            refine ⟨935422964799363006259079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 623615309866242004172719 935422964799363006259079)
            ·
              refine ⟨1403134447199044509388619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 935422964799363006259079 1403134447199044509388619)
              ·
                refine ⟨2104701670798566764082929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1403134447199044509388619 2104701670798566764082929)
                ·
                  refine ⟨1578526253098925073062197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2104701670798566764082929 1578526253098925073062197)
                  ·
                    refine ⟨147986836228024225599581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1578526253098925073062197 147986836228024225599581)
                    ·
                      rfl

theorem cell22_432305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 2, 5].length) (baseStart_432305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_432305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_432305 prefixEnd_432305 := by exact prefixLift 432305
  have htrace : WordTrace (prefixWord ++ tailWord_432305) baseStart_432305 baseEnd_432305 := by
    simpa [prefixWord, tailWord_432305, baseEnd_432305] using wordTrace_append hprefix tailTrace_432305
  have hstable : (prefixWord ++ tailWord_432305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432305).length < 2 ^ (prefixWord ++ tailWord_432305).sum := by decide
  have hdescent : baseEnd_432305 < baseStart_432305 := by decide
  rcases family_descends (prefixWord ++ tailWord_432305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432335 : List Nat := [1, 1, 2, 1, 1, 3, 6, 3, 4]
def baseStart_432335 : Nat := 118140960795 + 432335 * 2 ^ 59
def prefixEnd_432335 : Nat := 4983230072969 + 3 ^ 40 * 432335 * 2
def baseEnd_432335 : Nat := 49332368613704715783163

theorem tailTrace_432335 : CollatzResearch.WordTrace tailWord_432335 prefixEnd_432335 49332368613704715783163 := by
  unfold tailWord_432335
  simp only [CollatzResearch.WordTrace]
  refine ⟨15768552888731606784650459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10512368592487737856433639 15768552888731606784650459)
  ·
    refine ⟨23652829333097410176975689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15768552888731606784650459 23652829333097410176975689)
    ·
      refine ⟨17739621999823057632731767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23652829333097410176975689 17739621999823057632731767)
      ·
        refine ⟨26609432999734586449097651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17739621999823057632731767 26609432999734586449097651)
        ·
          refine ⟨39914149499601879673646477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26609432999734586449097651 39914149499601879673646477)
          ·
            refine ⟨14967806062350704877617429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39914149499601879673646477 14967806062350704877617429)
            ·
              refine ⟨701615909172689291138317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14967806062350704877617429 701615909172689291138317)
              ·
                refine ⟨263105965939758484176869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 701615909172689291138317 263105965939758484176869)
                ·
                  refine ⟨49332368613704715783163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 263105965939758484176869 49332368613704715783163)
                  ·
                    rfl

theorem cell22_432335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 3, 4].length) (baseStart_432335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_432335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_432335 prefixEnd_432335 := by exact prefixLift 432335
  have htrace : WordTrace (prefixWord ++ tailWord_432335) baseStart_432335 baseEnd_432335 := by
    simpa [prefixWord, tailWord_432335, baseEnd_432335] using wordTrace_append hprefix tailTrace_432335
  have hstable : (prefixWord ++ tailWord_432335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432335).length < 2 ^ (prefixWord ++ tailWord_432335).sum := by decide
  have hdescent : baseEnd_432335 < baseStart_432335 := by decide
  rcases family_descends (prefixWord ++ tailWord_432335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432380 : List Nat := [2, 2, 2, 1, 4, 1, 4, 6]
def baseStart_432380 : Nat := 118140960795 + 432380 * 2 ^ 59
def prefixEnd_432380 : Nat := 4983230072969 + 3 ^ 40 * 432380 * 2
def baseEnd_432380 : Nat := 16445834473416558886039

theorem tailTrace_432380 : CollatzResearch.WordTrace tailWord_432380 prefixEnd_432380 16445834473416558886039 := by
  unfold tailWord_432380
  simp only [CollatzResearch.WordTrace]
  refine ⟨7885097086784289735019297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10513462782379052980025729 7885097086784289735019297)
  ·
    refine ⟨5913822815088217301264473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7885097086784289735019297 5913822815088217301264473)
    ·
      refine ⟨4435367111316162975948355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5913822815088217301264473 4435367111316162975948355)
      ·
        refine ⟨6653050666974244463922533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4435367111316162975948355 6653050666974244463922533)
        ·
          refine ⟨1247447000057670836985475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6653050666974244463922533 1247447000057670836985475)
          ·
            refine ⟨1871170500086506255478213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1247447000057670836985475 1871170500086506255478213)
            ·
              refine ⟨350844468766219922902165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1871170500086506255478213 350844468766219922902165)
              ·
                refine ⟨16445834473416558886039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 350844468766219922902165 16445834473416558886039)
                ·
                  rfl

theorem cell22_432380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4, 6].length) (baseStart_432380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_432380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_432380 prefixEnd_432380 := by exact prefixLift 432380
  have htrace : WordTrace (prefixWord ++ tailWord_432380) baseStart_432380 baseEnd_432380 := by
    simpa [prefixWord, tailWord_432380, baseEnd_432380] using wordTrace_append hprefix tailTrace_432380
  have hstable : (prefixWord ++ tailWord_432380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432380).length < 2 ^ (prefixWord ++ tailWord_432380).sum := by decide
  have hdescent : baseEnd_432380 < baseStart_432380 := by decide
  rcases family_descends (prefixWord ++ tailWord_432380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432408 : List Nat := [2, 1, 2, 3, 1, 2, 1, 3, 7]
def baseStart_432408 : Nat := 118140960795 + 432408 * 2 ^ 59
def prefixEnd_432408 : Nat := 4983230072969 + 3 ^ 40 * 432408 * 2
def baseEnd_432408 : Nat := 49340698410988763424755

theorem tailTrace_432408 : CollatzResearch.WordTrace tailWord_432408 prefixEnd_432408 49340698410988763424755 := by
  unfold tailWord_432408
  simp only [CollatzResearch.WordTrace]
  refine ⟨7885607708733570126028939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10514143611644760168038585 7885607708733570126028939)
  ·
    refine ⟨11828411563100355189043409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7885607708733570126028939 11828411563100355189043409)
    ·
      refine ⟨8871308672325266391782557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11828411563100355189043409 8871308672325266391782557)
      ·
        refine ⟨3326740752121974896918459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8871308672325266391782557 3326740752121974896918459)
        ·
          refine ⟨4990111128182962345377689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3326740752121974896918459 4990111128182962345377689)
          ·
            refine ⟨3742583346137221759033267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4990111128182962345377689 3742583346137221759033267)
            ·
              refine ⟨5613875019205832638549901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3742583346137221759033267 5613875019205832638549901)
              ·
                refine ⟨2105203132202187239456213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5613875019205832638549901 2105203132202187239456213)
                ·
                  refine ⟨49340698410988763424755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2105203132202187239456213 49340698410988763424755)
                  ·
                    rfl

theorem cell22_432408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 7].length) (baseStart_432408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_432408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_432408 prefixEnd_432408 := by exact prefixLift 432408
  have htrace : WordTrace (prefixWord ++ tailWord_432408) baseStart_432408 baseEnd_432408 := by
    simpa [prefixWord, tailWord_432408, baseEnd_432408] using wordTrace_append hprefix tailTrace_432408
  have hstable : (prefixWord ++ tailWord_432408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432408).length < 2 ^ (prefixWord ++ tailWord_432408).sum := by decide
  have hdescent : baseEnd_432408 < baseStart_432408 := by decide
  rcases family_descends (prefixWord ++ tailWord_432408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432485 : List Nat := [1, 3, 1, 3, 1, 3, 1, 3, 1, 5]
def baseStart_432485 : Nat := 118140960795 + 432485 * 2 ^ 59
def prefixEnd_432485 : Nat := 4983230072969 + 3 ^ 40 * 432485 * 2
def baseEnd_432485 : Nat := 148048453906563756099029

theorem tailTrace_432485 : CollatzResearch.WordTrace tailWord_432485 prefixEnd_432485 148048453906563756099029 := by
  unfold tailWord_432485
  simp only [CollatzResearch.WordTrace]
  refine ⟨15774023838188182402610909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10516015892125454935073939 15774023838188182402610909)
  ·
    refine ⟨5915258939320568400979091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15774023838188182402610909 5915258939320568400979091)
    ·
      refine ⟨8872888408980852601468637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5915258939320568400979091 8872888408980852601468637)
      ·
        refine ⟨3327333153367819725550739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8872888408980852601468637 3327333153367819725550739)
        ·
          refine ⟨4990999730051729588326109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3327333153367819725550739 4990999730051729588326109)
          ·
            refine ⟨1871624898769398595622291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4990999730051729588326109 1871624898769398595622291)
            ·
              refine ⟨2807437348154097893433437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1871624898769398595622291 2807437348154097893433437)
              ·
                refine ⟨1052789005557786710037539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2807437348154097893433437 1052789005557786710037539)
                ·
                  refine ⟨1579183508336680065056309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1052789005557786710037539 1579183508336680065056309)
                  ·
                    refine ⟨148048453906563756099029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1579183508336680065056309 148048453906563756099029)
                    ·
                      rfl

theorem cell22_432485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3, 1, 5].length) (baseStart_432485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_432485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_432485 prefixEnd_432485 := by exact prefixLift 432485
  have htrace : WordTrace (prefixWord ++ tailWord_432485) baseStart_432485 baseEnd_432485 := by
    simpa [prefixWord, tailWord_432485, baseEnd_432485] using wordTrace_append hprefix tailTrace_432485
  have hstable : (prefixWord ++ tailWord_432485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432485).length < 2 ^ (prefixWord ++ tailWord_432485).sum := by decide
  have hdescent : baseEnd_432485 < baseStart_432485 := by decide
  rcases family_descends (prefixWord ++ tailWord_432485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432515 : List Nat := [1, 1, 1, 3, 6, 1, 9]
def baseStart_432515 : Nat := 118140960795 + 432515 * 2 ^ 59
def prefixEnd_432515 : Nat := 4983230072969 + 3 ^ 40 * 432515 * 2
def baseEnd_432515 : Nat := 5483656426653839920331

theorem tailTrace_432515 : CollatzResearch.WordTrace tailWord_432515 prefixEnd_432515 5483656426653839920331 := by
  unfold tailWord_432515
  simp only [CollatzResearch.WordTrace]
  refine ⟨15775118028079497526202999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10516745352052998350801999 15775118028079497526202999)
  ·
    refine ⟨23662677042119246289304499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15775118028079497526202999 23662677042119246289304499)
    ·
      refine ⟨35494015563178869433956749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23662677042119246289304499 35494015563178869433956749)
      ·
        refine ⟨13310255836192076037733781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35494015563178869433956749 13310255836192076037733781)
        ·
          refine ⟨623918242321503564268771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13310255836192076037733781 623918242321503564268771)
          ·
            refine ⟨935877363482255346403157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 623918242321503564268771 935877363482255346403157)
            ·
              refine ⟨5483656426653839920331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 935877363482255346403157 5483656426653839920331)
              ·
                rfl

theorem cell22_432515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 9].length) (baseStart_432515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_432515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_432515 prefixEnd_432515 := by exact prefixLift 432515
  have htrace : WordTrace (prefixWord ++ tailWord_432515) baseStart_432515 baseEnd_432515 := by
    simpa [prefixWord, tailWord_432515, baseEnd_432515] using wordTrace_append hprefix tailTrace_432515
  have hstable : (prefixWord ++ tailWord_432515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432515).length < 2 ^ (prefixWord ++ tailWord_432515).sum := by decide
  have hdescent : baseEnd_432515 < baseStart_432515 := by decide
  rcases family_descends (prefixWord ++ tailWord_432515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432536 : List Nat := [2, 1, 2, 5, 1, 2, 3, 1, 2, 3]
def baseStart_432536 : Nat := 118140960795 + 432536 * 2 ^ 59
def prefixEnd_432536 : Nat := 4983230072969 + 3 ^ 40 * 432536 * 2
def baseEnd_432536 : Nat := 148065912248816623073873

theorem tailTrace_432536 : CollatzResearch.WordTrace tailWord_432536 prefixEnd_432536 148065912248816623073873 := by
  unfold tailWord_432536
  simp only [CollatzResearch.WordTrace]
  refine ⟨7887941980501709056358731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10517255974002278741811641 7887941980501709056358731)
  ·
    refine ⟨11831912970752563584538097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7887941980501709056358731 11831912970752563584538097)
    ·
      refine ⟨8873934728064422688403573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11831912970752563584538097 8873934728064422688403573)
      ·
        refine ⟨831931380756039627037835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8873934728064422688403573 831931380756039627037835)
        ·
          refine ⟨1247897071134059440556753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 831931380756039627037835 1247897071134059440556753)
          ·
            refine ⟨935922803350544580417565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1247897071134059440556753 935922803350544580417565)
            ·
              refine ⟨350971051256454217656587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 935922803350544580417565 350971051256454217656587)
              ·
                refine ⟨526456576884681326484881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 350971051256454217656587 526456576884681326484881)
                ·
                  refine ⟨394842432663510994863661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 526456576884681326484881 394842432663510994863661)
                  ·
                    refine ⟨148065912248816623073873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 394842432663510994863661 148065912248816623073873)
                    ·
                      rfl

theorem cell22_432536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3, 1, 2, 3].length) (baseStart_432536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_432536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_432536 prefixEnd_432536 := by exact prefixLift 432536
  have htrace : WordTrace (prefixWord ++ tailWord_432536) baseStart_432536 baseEnd_432536 := by
    simpa [prefixWord, tailWord_432536, baseEnd_432536] using wordTrace_append hprefix tailTrace_432536
  have hstable : (prefixWord ++ tailWord_432536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432536).length < 2 ^ (prefixWord ++ tailWord_432536).sum := by decide
  have hdescent : baseEnd_432536 < baseStart_432536 := by decide
  rcases family_descends (prefixWord ++ tailWord_432536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432547 : List Nat := [1, 1, 1, 4, 1, 4, 2, 2, 3, 3]
def baseStart_432547 : Nat := 118140960795 + 432547 * 2 ^ 59
def prefixEnd_432547 : Nat := 4983230072969 + 3 ^ 40 * 432547 * 2
def baseEnd_432547 : Nat := 148069677773616261048839

theorem tailTrace_432547 : CollatzResearch.WordTrace tailWord_432547 prefixEnd_432547 148069677773616261048839 := by
  unfold tailWord_432547
  simp only [CollatzResearch.WordTrace]
  refine ⟨15776285163963566991367895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10517523442642377994245263 15776285163963566991367895)
  ·
    refine ⟨23664427745945350487051843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15776285163963566991367895 23664427745945350487051843)
    ·
      refine ⟨35496641618918025730577765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23664427745945350487051843 35496641618918025730577765)
      ·
        refine ⟨6655620303547129824483331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35496641618918025730577765 6655620303547129824483331)
        ·
          refine ⟨9983430455320694736724997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6655620303547129824483331 9983430455320694736724997)
          ·
            refine ⟨1871893210372630263135937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9983430455320694736724997 1871893210372630263135937)
            ·
              refine ⟨1403919907779472697351953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1871893210372630263135937 1403919907779472697351953)
              ·
                refine ⟨1052939930834604523013965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1403919907779472697351953 1052939930834604523013965)
                ·
                  refine ⟨394852474062976696130237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1052939930834604523013965 394852474062976696130237)
                  ·
                    refine ⟨148069677773616261048839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 394852474062976696130237 148069677773616261048839)
                    ·
                      rfl

theorem cell22_432547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 2, 3, 3].length) (baseStart_432547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_432547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_432547 prefixEnd_432547 := by exact prefixLift 432547
  have htrace : WordTrace (prefixWord ++ tailWord_432547) baseStart_432547 baseEnd_432547 := by
    simpa [prefixWord, tailWord_432547, baseEnd_432547] using wordTrace_append hprefix tailTrace_432547
  have hstable : (prefixWord ++ tailWord_432547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432547).length < 2 ^ (prefixWord ++ tailWord_432547).sum := by decide
  have hdescent : baseEnd_432547 < baseStart_432547 := by decide
  rcases family_descends (prefixWord ++ tailWord_432547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432590 : List Nat := [4, 1, 1, 1, 2, 1, 1, 1, 2, 8]
def baseStart_432590 : Nat := 118140960795 + 432590 * 2 ^ 59
def prefixEnd_432590 : Nat := 4983230072969 + 3 ^ 40 * 432590 * 2
def baseEnd_432590 : Nat := 148084397552378482223707

theorem tailTrace_432590 : CollatzResearch.WordTrace tailWord_432590 prefixEnd_432590 148084397552378482223707 := by
  unfold tailWord_432590
  simp only [CollatzResearch.WordTrace]
  refine ⟨1972231687850973166897903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10518569001871856890122149 1972231687850973166897903)
  ·
    refine ⟨2958347531776459750346855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1972231687850973166897903 2958347531776459750346855)
    ·
      refine ⟨4437521297664689625520283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2958347531776459750346855 4437521297664689625520283)
      ·
        refine ⟨6656281946497034438280425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4437521297664689625520283 6656281946497034438280425)
        ·
          refine ⟨4992211459872775828710319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6656281946497034438280425 4992211459872775828710319)
          ·
            refine ⟨7488317189809163743065479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4992211459872775828710319 7488317189809163743065479)
            ·
              refine ⟨11232475784713745614598219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7488317189809163743065479 11232475784713745614598219)
              ·
                refine ⟨16848713677070618421897329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11232475784713745614598219 16848713677070618421897329)
                ·
                  refine ⟨12636535257802963816422997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16848713677070618421897329 12636535257802963816422997)
                  ·
                    refine ⟨148084397552378482223707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 12636535257802963816422997 148084397552378482223707)
                    ·
                      rfl

theorem cell22_432590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_432590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_432590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_432590 prefixEnd_432590 := by exact prefixLift 432590
  have htrace : WordTrace (prefixWord ++ tailWord_432590) baseStart_432590 baseEnd_432590 := by
    simpa [prefixWord, tailWord_432590, baseEnd_432590] using wordTrace_append hprefix tailTrace_432590
  have hstable : (prefixWord ++ tailWord_432590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432590).length < 2 ^ (prefixWord ++ tailWord_432590).sum := by decide
  have hdescent : baseEnd_432590 < baseStart_432590 := by decide
  rcases family_descends (prefixWord ++ tailWord_432590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432607 : List Nat := [1, 1, 2, 3, 3, 3, 1, 1, 3, 4]
def baseStart_432607 : Nat := 118140960795 + 432607 * 2 ^ 59
def prefixEnd_432607 : Nat := 4983230072969 + 3 ^ 40 * 432607 * 2
def baseEnd_432607 : Nat := 148090216999796104548655

theorem tailTrace_432607 : CollatzResearch.WordTrace tailWord_432607 prefixEnd_432607 148090216999796104548655 := by
  unfold tailWord_432607
  simp only [CollatzResearch.WordTrace]
  refine ⟨15778473543746197238552075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10518982362497464825701383 15778473543746197238552075)
  ·
    refine ⟨23667710315619295857828113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15778473543746197238552075 23667710315619295857828113)
    ·
      refine ⟨17750782736714471893371085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23667710315619295857828113 17750782736714471893371085)
      ·
        refine ⟨6656543526267926960014157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17750782736714471893371085 6656543526267926960014157)
        ·
          refine ⟨2496203822350472610005309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6656543526267926960014157 2496203822350472610005309)
          ·
            refine ⟨936076433381427228751991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2496203822350472610005309 936076433381427228751991)
            ·
              refine ⟨1404114650072140843127987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 936076433381427228751991 1404114650072140843127987)
              ·
                refine ⟨2106171975108211264691981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1404114650072140843127987 2106171975108211264691981)
                ·
                  refine ⟨789814490665579224259493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2106171975108211264691981 789814490665579224259493)
                  ·
                    refine ⟨148090216999796104548655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 789814490665579224259493 148090216999796104548655)
                    ·
                      rfl

theorem cell22_432607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 3, 4].length) (baseStart_432607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_432607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_432607 prefixEnd_432607 := by exact prefixLift 432607
  have htrace : WordTrace (prefixWord ++ tailWord_432607) baseStart_432607 baseEnd_432607 := by
    simpa [prefixWord, tailWord_432607, baseEnd_432607] using wordTrace_append hprefix tailTrace_432607
  have hstable : (prefixWord ++ tailWord_432607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432607).length < 2 ^ (prefixWord ++ tailWord_432607).sum := by decide
  have hdescent : baseEnd_432607 < baseStart_432607 := by decide
  rcases family_descends (prefixWord ++ tailWord_432607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432624 : List Nat := [2, 1, 1, 1, 3, 3, 5, 1, 1, 4]
def baseStart_432624 : Nat := 118140960795 + 432624 * 2 ^ 59
def prefixEnd_432624 : Nat := 4983230072969 + 3 ^ 40 * 432624 * 2
def baseEnd_432624 : Nat := 148096036447213726873603

theorem tailTrace_432624 : CollatzResearch.WordTrace tailWord_432624 prefixEnd_432624 148096036447213726873603 := by
  unfold tailWord_432624
  simp only [CollatzResearch.WordTrace]
  refine ⟨7889546792342304570960463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10519395723123072761280617 7889546792342304570960463)
  ·
    refine ⟨11834320188513456856440695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7889546792342304570960463 11834320188513456856440695)
    ·
      refine ⟨17751480282770185284661043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11834320188513456856440695 17751480282770185284661043)
      ·
        refine ⟨26627220424155277926991565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17751480282770185284661043 26627220424155277926991565)
        ·
          refine ⟨9985207659058229222621837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26627220424155277926991565 9985207659058229222621837)
          ·
            refine ⟨3744452872146835958483189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9985207659058229222621837 3744452872146835958483189)
            ·
              refine ⟨351042456763765871107799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3744452872146835958483189 351042456763765871107799)
              ·
                refine ⟨526563685145648806661699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 351042456763765871107799 526563685145648806661699)
                ·
                  refine ⟨789845527718473209992549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 526563685145648806661699 789845527718473209992549)
                  ·
                    refine ⟨148096036447213726873603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 789845527718473209992549 148096036447213726873603)
                    ·
                      rfl

theorem cell22_432624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5, 1, 1, 4].length) (baseStart_432624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_432624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_432624 prefixEnd_432624 := by exact prefixLift 432624
  have htrace : WordTrace (prefixWord ++ tailWord_432624) baseStart_432624 baseEnd_432624 := by
    simpa [prefixWord, tailWord_432624, baseEnd_432624] using wordTrace_append hprefix tailTrace_432624
  have hstable : (prefixWord ++ tailWord_432624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432624).length < 2 ^ (prefixWord ++ tailWord_432624).sum := by decide
  have hdescent : baseEnd_432624 < baseStart_432624 := by decide
  rcases family_descends (prefixWord ++ tailWord_432624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432654 : List Nat := [4, 1, 1, 2, 3, 2, 2, 1, 1, 5]
def baseStart_432654 : Nat := 118140960795 + 432654 * 2 ^ 59
def prefixEnd_432654 : Nat := 4983230072969 + 3 ^ 40 * 432654 * 2
def baseEnd_432654 : Nat := 148106306060303648623511

theorem tailTrace_432654 : CollatzResearch.WordTrace tailWord_432654 prefixEnd_432654 148106306060303648623511 := by
  unfold tailWord_432654
  simp only [CollatzResearch.WordTrace]
  refine ⟨1972523471821990533189127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10520125183050616177008677 1972523471821990533189127)
  ·
    refine ⟨2958785207732985799783691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1972523471821990533189127 2958785207732985799783691)
    ·
      refine ⟨4438177811599478699675537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2958785207732985799783691 4438177811599478699675537)
      ·
        refine ⟨3328633358699609024756653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4438177811599478699675537 3328633358699609024756653)
        ·
          refine ⟨1248237509512353384283745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3328633358699609024756653 1248237509512353384283745)
          ·
            refine ⟨936178132134265038212809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1248237509512353384283745 936178132134265038212809)
            ·
              refine ⟨702133599100698778659607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 936178132134265038212809 702133599100698778659607)
              ·
                refine ⟨1053200398651048167989411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 702133599100698778659607 1053200398651048167989411)
                ·
                  refine ⟨1579800597976572251984117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1053200398651048167989411 1579800597976572251984117)
                  ·
                    refine ⟨148106306060303648623511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1579800597976572251984117 148106306060303648623511)
                    ·
                      rfl

theorem cell22_432654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 1, 1, 5].length) (baseStart_432654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_432654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_432654 prefixEnd_432654 := by exact prefixLift 432654
  have htrace : WordTrace (prefixWord ++ tailWord_432654) baseStart_432654 baseEnd_432654 := by
    simpa [prefixWord, tailWord_432654, baseEnd_432654] using wordTrace_append hprefix tailTrace_432654
  have hstable : (prefixWord ++ tailWord_432654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432654).length < 2 ^ (prefixWord ++ tailWord_432654).sum := by decide
  have hdescent : baseEnd_432654 < baseStart_432654 := by decide
  rcases family_descends (prefixWord ++ tailWord_432654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432665 : List Nat := [1, 2, 1, 2, 1, 1, 2, 3, 2, 7]
def baseStart_432665 : Nat := 118140960795 + 432665 * 2 ^ 59
def prefixEnd_432665 : Nat := 4983230072969 + 3 ^ 40 * 432665 * 2
def baseEnd_432665 : Nat := 148110071585103286598477

theorem tailTrace_432665 : CollatzResearch.WordTrace tailWord_432665 prefixEnd_432665 148110071585103286598477 := by
  unfold tailWord_432665
  simp only [CollatzResearch.WordTrace]
  refine ⟨15780588977536073144163449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10520392651690715429442299 15780588977536073144163449)
  ·
    refine ⟨11835441733152054858122587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15780588977536073144163449 11835441733152054858122587)
    ·
      refine ⟨17753162599728082287183881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11835441733152054858122587 17753162599728082287183881)
      ·
        refine ⟨13314871949796061715387911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17753162599728082287183881 13314871949796061715387911)
        ·
          refine ⟨19972307924694092573081867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13314871949796061715387911 19972307924694092573081867)
          ·
            refine ⟨29958461887041138859622801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19972307924694092573081867 29958461887041138859622801)
            ·
              refine ⟨22468846415280854144717101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29958461887041138859622801 22468846415280854144717101)
              ·
                refine ⟨8425817405730320304268913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22468846415280854144717101 8425817405730320304268913)
                ·
                  refine ⟨6319363054297740228201685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8425817405730320304268913 6319363054297740228201685)
                  ·
                    refine ⟨148110071585103286598477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6319363054297740228201685 148110071585103286598477)
                    ·
                      rfl

theorem cell22_432665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 7].length) (baseStart_432665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_432665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_432665 prefixEnd_432665 := by exact prefixLift 432665
  have htrace : WordTrace (prefixWord ++ tailWord_432665) baseStart_432665 baseEnd_432665 := by
    simpa [prefixWord, tailWord_432665, baseEnd_432665] using wordTrace_append hprefix tailTrace_432665
  have hstable : (prefixWord ++ tailWord_432665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432665).length < 2 ^ (prefixWord ++ tailWord_432665).sum := by decide
  have hdescent : baseEnd_432665 < baseStart_432665 := by decide
  rcases family_descends (prefixWord ++ tailWord_432665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432669 : List Nat := [1, 4, 2, 2, 1, 2, 3, 1, 2, 4]
def baseStart_432669 : Nat := 118140960795 + 432669 * 2 ^ 59
def prefixEnd_432669 : Nat := 4983230072969 + 3 ^ 40 * 432669 * 2
def baseEnd_432669 : Nat := 148111440866848609498465

theorem tailTrace_432669 : CollatzResearch.WordTrace tailWord_432669 prefixEnd_432669 148111440866848609498465 := by
  unfold tailWord_432669
  simp only [CollatzResearch.WordTrace]
  refine ⟨15780734869521581827309061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10520489913014387884872707 15780734869521581827309061)
  ·
    refine ⟨2958887788035296592620449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15780734869521581827309061 2958887788035296592620449)
    ·
      refine ⟨2219165841026472444465337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2958887788035296592620449 2219165841026472444465337)
      ·
        refine ⟨1664374380769854333349003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2219165841026472444465337 1664374380769854333349003)
        ·
          refine ⟨2496561571154781500023505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1664374380769854333349003 2496561571154781500023505)
          ·
            refine ⟨1872421178366086125017629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2496561571154781500023505 1872421178366086125017629)
            ·
              refine ⟨702157941887282296881611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1872421178366086125017629 702157941887282296881611)
              ·
                refine ⟨1053236912830923445322417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 702157941887282296881611 1053236912830923445322417)
                ·
                  refine ⟨789927684623192583991813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1053236912830923445322417 789927684623192583991813)
                  ·
                    refine ⟨148111440866848609498465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 789927684623192583991813 148111440866848609498465)
                    ·
                      rfl

theorem cell22_432669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_432669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_432669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_432669 prefixEnd_432669 := by exact prefixLift 432669
  have htrace : WordTrace (prefixWord ++ tailWord_432669) baseStart_432669 baseEnd_432669 := by
    simpa [prefixWord, tailWord_432669, baseEnd_432669] using wordTrace_append hprefix tailTrace_432669
  have hstable : (prefixWord ++ tailWord_432669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432669).length < 2 ^ (prefixWord ++ tailWord_432669).sum := by decide
  have hdescent : baseEnd_432669 < baseStart_432669 := by decide
  rcases family_descends (prefixWord ++ tailWord_432669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432712 : List Nat := [2, 1, 3, 1, 1, 1, 1, 7, 5]
def baseStart_432712 : Nat := 118140960795 + 432712 * 2 ^ 59
def prefixEnd_432712 : Nat := 4983230072969 + 3 ^ 40 * 432712 * 2
def baseEnd_432712 : Nat := 49375386881870276891111

theorem tailTrace_432712 : CollatzResearch.WordTrace tailWord_432712 prefixEnd_432712 49375386881870276891111 := by
  unfold tailWord_432712
  simp only [CollatzResearch.WordTrace]
  refine ⟨7891151604182900085562195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10521535472243866780749593 7891151604182900085562195)
  ·
    refine ⟨11836727406274350128343293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7891151604182900085562195 11836727406274350128343293)
    ·
      refine ⟨4438772777352881298128735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11836727406274350128343293 4438772777352881298128735)
      ·
        refine ⟨6658159166029321947193103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4438772777352881298128735 6658159166029321947193103)
        ·
          refine ⟨9987238749043982920789655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6658159166029321947193103 9987238749043982920789655)
          ·
            refine ⟨14980858123565974381184483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9987238749043982920789655 14980858123565974381184483)
            ·
              refine ⟨22471287185348961571776725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14980858123565974381184483 22471287185348961571776725)
              ·
                refine ⟨526670793406616286838517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 22471287185348961571776725 526670793406616286838517)
                ·
                  refine ⟨49375386881870276891111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 526670793406616286838517 49375386881870276891111)
                  ·
                    rfl

theorem cell22_432712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 7, 5].length) (baseStart_432712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_432712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_432712 prefixEnd_432712 := by exact prefixLift 432712
  have htrace : WordTrace (prefixWord ++ tailWord_432712) baseStart_432712 baseEnd_432712 := by
    simpa [prefixWord, tailWord_432712, baseEnd_432712] using wordTrace_append hprefix tailTrace_432712
  have hstable : (prefixWord ++ tailWord_432712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432712).length < 2 ^ (prefixWord ++ tailWord_432712).sum := by decide
  have hdescent : baseEnd_432712 < baseStart_432712 := by decide
  rcases family_descends (prefixWord ++ tailWord_432712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432750 : List Nat := [4, 1, 2, 2, 2, 2, 3, 2, 1, 3]
def baseStart_432750 : Nat := 118140960795 + 432750 * 2 ^ 59
def prefixEnd_432750 : Nat := 4983230072969 + 3 ^ 40 * 432750 * 2
def baseEnd_432750 : Nat := 148139168822191398223217

theorem tailTrace_432750 : CollatzResearch.WordTrace tailWord_432750 prefixEnd_432750 148139168822191398223217 := by
  unfold tailWord_432750
  simp only [CollatzResearch.WordTrace]
  refine ⟨1972961147778516582625963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10522459454818755107338469 1972961147778516582625963)
  ·
    refine ⟨2959441721667774873938945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1972961147778516582625963 2959441721667774873938945)
    ·
      refine ⟨2219581291250831155454209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2959441721667774873938945 2219581291250831155454209)
      ·
        refine ⟨1664685968438123366590657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2219581291250831155454209 1664685968438123366590657)
        ·
          refine ⟨1248514476328592524942993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1664685968438123366590657 1248514476328592524942993)
          ·
            refine ⟨936385857246444393707245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1248514476328592524942993 936385857246444393707245)
            ·
              refine ⟨351144696467416647640217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 936385857246444393707245 351144696467416647640217)
              ·
                refine ⟨263358522350562485730163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 351144696467416647640217 263358522350562485730163)
                ·
                  refine ⟨395037783525843728595245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 263358522350562485730163 395037783525843728595245)
                  ·
                    refine ⟨148139168822191398223217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 395037783525843728595245 148139168822191398223217)
                    ·
                      rfl

theorem cell22_432750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3, 2, 1, 3].length) (baseStart_432750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_432750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_432750 prefixEnd_432750 := by exact prefixLift 432750
  have htrace : WordTrace (prefixWord ++ tailWord_432750) baseStart_432750 baseEnd_432750 := by
    simpa [prefixWord, tailWord_432750, baseEnd_432750] using wordTrace_append hprefix tailTrace_432750
  have hstable : (prefixWord ++ tailWord_432750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432750).length < 2 ^ (prefixWord ++ tailWord_432750).sum := by decide
  have hdescent : baseEnd_432750 < baseStart_432750 := by decide
  rcases family_descends (prefixWord ++ tailWord_432750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432787 : List Nat := [1, 1, 1, 2, 1, 2, 2, 2, 6, 4]
def baseStart_432787 : Nat := 118140960795 + 432787 * 2 ^ 59
def prefixEnd_432787 : Nat := 4983230072969 + 3 ^ 40 * 432787 * 2
def baseEnd_432787 : Nat := 148151834678335635048103

theorem tailTrace_432787 : CollatzResearch.WordTrace tailWord_432787 prefixEnd_432787 148151834678335635048103 := by
  unfold tailWord_432787
  simp only [CollatzResearch.WordTrace]
  refine ⟨15785038683094087980104615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10523359122062725320069743 15785038683094087980104615)
  ·
    refine ⟨23677558024641131970156923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15785038683094087980104615 23677558024641131970156923)
    ·
      refine ⟨35516337036961697955235385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23677558024641131970156923 35516337036961697955235385)
      ·
        refine ⟨26637252777721273466426539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35516337036961697955235385 26637252777721273466426539)
        ·
          refine ⟨39955879166581910199639809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26637252777721273466426539 39955879166581910199639809)
          ·
            refine ⟨29966909374936432649729857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39955879166581910199639809 29966909374936432649729857)
            ·
              refine ⟨22475182031202324487297393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29966909374936432649729857 22475182031202324487297393)
              ·
                refine ⟨16856386523401743365473045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22475182031202324487297393 16856386523401743365473045)
                ·
                  refine ⟨790143118284456720256549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 16856386523401743365473045 790143118284456720256549)
                  ·
                    refine ⟨148151834678335635048103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 790143118284456720256549 148151834678335635048103)
                    ·
                      rfl

theorem cell22_432787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 6, 4].length) (baseStart_432787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_432787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_432787 prefixEnd_432787 := by exact prefixLift 432787
  have htrace : WordTrace (prefixWord ++ tailWord_432787) baseStart_432787 baseEnd_432787 := by
    simpa [prefixWord, tailWord_432787, baseEnd_432787] using wordTrace_append hprefix tailTrace_432787
  have hstable : (prefixWord ++ tailWord_432787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432787).length < 2 ^ (prefixWord ++ tailWord_432787).sum := by decide
  have hdescent : baseEnd_432787 < baseStart_432787 := by decide
  rcases family_descends (prefixWord ++ tailWord_432787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432802 : List Nat := [3, 3, 1, 15]
def baseStart_432802 : Nat := 118140960795 + 432802 * 2 ^ 59
def prefixEnd_432802 : Nat := 4983230072969 + 3 ^ 40 * 432802 * 2
def baseEnd_432802 : Nat := 203233154300247731033

theorem tailTrace_432802 : CollatzResearch.WordTrace tailWord_432802 prefixEnd_432802 203233154300247731033 := by
  unfold tailWord_432802
  simp only [CollatzResearch.WordTrace]
  refine ⟨3946396444509936385475165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10523723852026497027933773 3946396444509936385475165)
  ·
    refine ⟨1479898666691226144553187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3946396444509936385475165 1479898666691226144553187)
    ·
      refine ⟨2219848000036839216829781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1479898666691226144553187 2219848000036839216829781)
      ·
        refine ⟨203233154300247731033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 15 2219848000036839216829781 203233154300247731033)
        ·
          rfl

theorem cell22_432802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 15].length) (baseStart_432802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_432802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_432802 prefixEnd_432802 := by exact prefixLift 432802
  have htrace : WordTrace (prefixWord ++ tailWord_432802) baseStart_432802 baseEnd_432802 := by
    simpa [prefixWord, tailWord_432802, baseEnd_432802] using wordTrace_append hprefix tailTrace_432802
  have hstable : (prefixWord ++ tailWord_432802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432802).length < 2 ^ (prefixWord ++ tailWord_432802).sum := by decide
  have hdescent : baseEnd_432802 < baseStart_432802 := by decide
  rcases family_descends (prefixWord ++ tailWord_432802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432804 : List Nat := [2, 3, 1, 2, 2, 1, 1, 4, 2, 4]
def baseStart_432804 : Nat := 118140960795 + 432804 * 2 ^ 59
def prefixEnd_432804 : Nat := 4983230072969 + 3 ^ 40 * 432804 * 2
def baseEnd_432804 : Nat := 148157654125753257373051

theorem tailTrace_432804 : CollatzResearch.WordTrace tailWord_432804 prefixEnd_432804 148157654125753257373051 := by
  unfold tailWord_432804
  simp only [CollatzResearch.WordTrace]
  refine ⟨7892829362016249941736733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10523772482688333255648977 7892829362016249941736733)
  ·
    refine ⟨2959811010756093728151275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7892829362016249941736733 2959811010756093728151275)
    ·
      refine ⟨4439716516134140592226913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2959811010756093728151275 4439716516134140592226913)
      ·
        refine ⟨3329787387100605444170185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4439716516134140592226913 3329787387100605444170185)
        ·
          refine ⟨2497340540325454083127639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3329787387100605444170185 2497340540325454083127639)
          ·
            refine ⟨3746010810488181124691459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2497340540325454083127639 3746010810488181124691459)
            ·
              refine ⟨5619016215732271687037189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3746010810488181124691459 5619016215732271687037189)
              ·
                refine ⟨1053565540449800941319473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5619016215732271687037189 1053565540449800941319473)
                ·
                  refine ⟨790174155337350705989605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1053565540449800941319473 790174155337350705989605)
                  ·
                    refine ⟨148157654125753257373051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 790174155337350705989605 148157654125753257373051)
                    ·
                      rfl

theorem cell22_432804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_432804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_432804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_432804 prefixEnd_432804 := by exact prefixLift 432804
  have htrace : WordTrace (prefixWord ++ tailWord_432804) baseStart_432804 baseEnd_432804 := by
    simpa [prefixWord, tailWord_432804, baseEnd_432804] using wordTrace_append hprefix tailTrace_432804
  have hstable : (prefixWord ++ tailWord_432804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432804).length < 2 ^ (prefixWord ++ tailWord_432804).sum := by decide
  have hdescent : baseEnd_432804 < baseStart_432804 := by decide
  rcases family_descends (prefixWord ++ tailWord_432804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432819 : List Nat := [1, 1, 1, 2, 3, 6, 1, 7]
def baseStart_432819 : Nat := 118140960795 + 432819 * 2 ^ 59
def prefixEnd_432819 : Nat := 4983230072969 + 3 ^ 40 * 432819 * 2
def baseEnd_432819 : Nat := 16462532103588690916445

theorem tailTrace_432819 : CollatzResearch.WordTrace tailWord_432819 prefixEnd_432819 16462532103588690916445 := by
  unfold tailWord_432819
  simp only [CollatzResearch.WordTrace]
  refine ⟨15786205818978157445269511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10524137212652104963513007 15786205818978157445269511)
  ·
    refine ⟨23679308728467236167904267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15786205818978157445269511 23679308728467236167904267)
    ·
      refine ⟨35518963092700854251856401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23679308728467236167904267 35518963092700854251856401)
      ·
        refine ⟨26639222319525640688892301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35518963092700854251856401 26639222319525640688892301)
        ·
          refine ⟨9989708369822115258334613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26639222319525640688892301 9989708369822115258334613)
          ·
            refine ⟨468267579835411652734435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9989708369822115258334613 468267579835411652734435)
            ·
              refine ⟨702401369753117479101653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 468267579835411652734435 702401369753117479101653)
              ·
                refine ⟨16462532103588690916445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 702401369753117479101653 16462532103588690916445)
                ·
                  rfl

theorem cell22_432819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 7].length) (baseStart_432819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_432819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_432819 prefixEnd_432819 := by exact prefixLift 432819
  have htrace : WordTrace (prefixWord ++ tailWord_432819) baseStart_432819 baseEnd_432819 := by
    simpa [prefixWord, tailWord_432819, baseEnd_432819] using wordTrace_append hprefix tailTrace_432819
  have hstable : (prefixWord ++ tailWord_432819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432819).length < 2 ^ (prefixWord ++ tailWord_432819).sum := by decide
  have hdescent : baseEnd_432819 < baseStart_432819 := by decide
  rcases family_descends (prefixWord ++ tailWord_432819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432836 : List Nat := [2, 3, 3, 1, 1, 3, 3, 6]
def baseStart_432836 : Nat := 118140960795 + 432836 * 2 ^ 59
def prefixEnd_432836 : Nat := 4983230072969 + 3 ^ 40 * 432836 * 2
def baseEnd_432836 : Nat := 16463178708857315619217

theorem tailTrace_432836 : CollatzResearch.WordTrace tailWord_432836 prefixEnd_432836 16463178708857315619217 := by
  unfold tailWord_432836
  simp only [CollatzResearch.WordTrace]
  refine ⟨7893412929958284674319181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10524550573277712899092241 7893412929958284674319181)
  ·
    refine ⟨2960029848734356752869693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7893412929958284674319181 2960029848734356752869693)
    ·
      refine ⟨1110011193275383782326135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2960029848734356752869693 1110011193275383782326135)
      ·
        refine ⟨1665016789913075673489203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1110011193275383782326135 1665016789913075673489203)
        ·
          refine ⟨2497525184869613510233805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1665016789913075673489203 2497525184869613510233805)
          ·
            refine ⟨936571944326105066337677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2497525184869613510233805 936571944326105066337677)
            ·
              refine ⟨351214479122289399876629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 936571944326105066337677 351214479122289399876629)
              ·
                refine ⟨16463178708857315619217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 351214479122289399876629 16463178708857315619217)
                ·
                  rfl

theorem cell22_432836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3, 6].length) (baseStart_432836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_432836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_432836 prefixEnd_432836 := by exact prefixLift 432836
  have htrace : WordTrace (prefixWord ++ tailWord_432836) baseStart_432836 baseEnd_432836 := by
    simpa [prefixWord, tailWord_432836, baseEnd_432836] using wordTrace_append hprefix tailTrace_432836
  have hstable : (prefixWord ++ tailWord_432836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432836).length < 2 ^ (prefixWord ++ tailWord_432836).sum := by decide
  have hdescent : baseEnd_432836 < baseStart_432836 := by decide
  rcases family_descends (prefixWord ++ tailWord_432836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432868 : List Nat := [2, 3, 1, 1, 1, 4, 2, 4, 1, 3]
def baseStart_432868 : Nat := 118140960795 + 432868 * 2 ^ 59
def prefixEnd_432868 : Nat := 4983230072969 + 3 ^ 40 * 432868 * 2
def baseEnd_432868 : Nat := 148179562633678423772855

theorem tailTrace_432868 : CollatzResearch.WordTrace tailWord_432868 prefixEnd_432868 148179562633678423772855 := by
  unfold tailWord_432868
  simp only [CollatzResearch.WordTrace]
  refine ⟨7893996497900319406901629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10525328663867092542535505 7893996497900319406901629)
  ·
    refine ⟨2960248686712619777588111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7893996497900319406901629 2960248686712619777588111)
    ·
      refine ⟨4440373030068929666382167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2960248686712619777588111 4440373030068929666382167)
      ·
        refine ⟨6660559545103394499573251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4440373030068929666382167 6660559545103394499573251)
        ·
          refine ⟨9990839317655091749359877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6660559545103394499573251 9990839317655091749359877)
          ·
            refine ⟨1873282372060329703004977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9990839317655091749359877 1873282372060329703004977)
            ·
              refine ⟨1404961779045247277253733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1873282372060329703004977 1404961779045247277253733)
              ·
                refine ⟨263430333570983864485075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1404961779045247277253733 263430333570983864485075)
                ·
                  refine ⟨395145500356475796727613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 263430333570983864485075 395145500356475796727613)
                  ·
                    refine ⟨148179562633678423772855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 395145500356475796727613 148179562633678423772855)
                    ·
                      rfl

theorem cell22_432868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 4, 1, 3].length) (baseStart_432868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_432868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_432868 prefixEnd_432868 := by exact prefixLift 432868
  have htrace : WordTrace (prefixWord ++ tailWord_432868) baseStart_432868 baseEnd_432868 := by
    simpa [prefixWord, tailWord_432868, baseEnd_432868] using wordTrace_append hprefix tailTrace_432868
  have hstable : (prefixWord ++ tailWord_432868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432868).length < 2 ^ (prefixWord ++ tailWord_432868).sum := by decide
  have hdescent : baseEnd_432868 < baseStart_432868 := by decide
  rcases family_descends (prefixWord ++ tailWord_432868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432879 : List Nat := [1, 1, 2, 1, 5, 2, 2, 1, 2, 5]
def baseStart_432879 : Nat := 118140960795 + 432879 * 2 ^ 59
def prefixEnd_432879 : Nat := 4983230072969 + 3 ^ 40 * 432879 * 2
def baseEnd_432879 : Nat := 148183328158478061747821

theorem tailTrace_432879 : CollatzResearch.WordTrace tailWord_432879 prefixEnd_432879 148183328158478061747821 := by
  unfold tailWord_432879
  simp only [CollatzResearch.WordTrace]
  refine ⟨15788394198760787692453691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10525596132507191794969127 15788394198760787692453691)
  ·
    refine ⟨23682591298141181538680537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15788394198760787692453691 23682591298141181538680537)
    ·
      refine ⟨17761943473605886154010403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23682591298141181538680537 17761943473605886154010403)
      ·
        refine ⟨26642915210408829231015605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17761943473605886154010403 26642915210408829231015605)
        ·
          refine ⟨2497773300975827740407713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26642915210408829231015605 2497773300975827740407713)
          ·
            refine ⟨1873329975731870805305785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2497773300975827740407713 1873329975731870805305785)
            ·
              refine ⟨1404997481798903103979339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1873329975731870805305785 1404997481798903103979339)
              ·
                refine ⟨2107496222698354655969009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1404997481798903103979339 2107496222698354655969009)
                ·
                  refine ⟨1580622167023765991976757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2107496222698354655969009 1580622167023765991976757)
                  ·
                    refine ⟨148183328158478061747821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1580622167023765991976757 148183328158478061747821)
                    ·
                      rfl

theorem cell22_432879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 2, 5].length) (baseStart_432879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_432879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_432879 prefixEnd_432879 := by exact prefixLift 432879
  have htrace : WordTrace (prefixWord ++ tailWord_432879) baseStart_432879 baseEnd_432879 := by
    simpa [prefixWord, tailWord_432879, baseEnd_432879] using wordTrace_append hprefix tailTrace_432879
  have hstable : (prefixWord ++ tailWord_432879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432879).length < 2 ^ (prefixWord ++ tailWord_432879).sum := by decide
  have hdescent : baseEnd_432879 < baseStart_432879 := by decide
  rcases family_descends (prefixWord ++ tailWord_432879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432881 : List Nat := [1, 2, 2, 2, 2, 2, 5, 1, 5]
def baseStart_432881 : Nat := 118140960795 + 432881 * 2 ^ 59
def prefixEnd_432881 : Nat := 4983230072969 + 3 ^ 40 * 432881 * 2
def baseEnd_432881 : Nat := 49394670933116907732605

theorem tailTrace_432881 : CollatzResearch.WordTrace tailWord_432881 prefixEnd_432881 49394670933116907732605 := by
  unfold tailWord_432881
  simp only [CollatzResearch.WordTrace]
  refine ⟨15788467144753542034026497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10525644763169028022684331 15788467144753542034026497)
  ·
    refine ⟨11841350358565156525519873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15788467144753542034026497 11841350358565156525519873)
    ·
      refine ⟨8881012768923867394139905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11841350358565156525519873 8881012768923867394139905)
      ·
        refine ⟨6660759576692900545604929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8881012768923867394139905 6660759576692900545604929)
        ·
          refine ⟨4995569682519675409203697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6660759576692900545604929 4995569682519675409203697)
          ·
            refine ⟨3746677261889756556902773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4995569682519675409203697 3746677261889756556902773)
            ·
              refine ⟨351250993302164677209635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3746677261889756556902773 351250993302164677209635)
              ·
                refine ⟨526876489953247015814453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 351250993302164677209635 526876489953247015814453)
                ·
                  refine ⟨49394670933116907732605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 526876489953247015814453 49394670933116907732605)
                  ·
                    rfl

theorem cell22_432881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5, 1, 5].length) (baseStart_432881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_432881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_432881 prefixEnd_432881 := by exact prefixLift 432881
  have htrace : WordTrace (prefixWord ++ tailWord_432881) baseStart_432881 baseEnd_432881 := by
    simpa [prefixWord, tailWord_432881, baseEnd_432881] using wordTrace_append hprefix tailTrace_432881
  have hstable : (prefixWord ++ tailWord_432881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432881).length < 2 ^ (prefixWord ++ tailWord_432881).sum := by decide
  have hdescent : baseEnd_432881 < baseStart_432881 := by decide
  rcases family_descends (prefixWord ++ tailWord_432881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432958 : List Nat := [4, 2, 1, 2, 3, 1, 1, 2, 1, 5]
def baseStart_432958 : Nat := 118140960795 + 432958 * 2 ^ 59
def prefixEnd_432958 : Nat := 4983230072969 + 3 ^ 40 * 432958 * 2
def baseEnd_432958 : Nat := 148210371472948189022579

theorem tailTrace_432958 : CollatzResearch.WordTrace tailWord_432958 prefixEnd_432958 148210371472948189022579 := by
  unfold tailWord_432958
  simp only [CollatzResearch.WordTrace]
  refine ⟨1973909445684323023072441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10527517043649722789719685 1973909445684323023072441)
  ·
    refine ⟨1480432084263242267304331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1973909445684323023072441 1480432084263242267304331)
    ·
      refine ⟨2220648126394863400956497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1480432084263242267304331 2220648126394863400956497)
      ·
        refine ⟨1665486094796147550717373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2220648126394863400956497 1665486094796147550717373)
        ·
          refine ⟨624557285548555331519015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1665486094796147550717373 624557285548555331519015)
          ·
            refine ⟨936835928322832997278523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 624557285548555331519015 936835928322832997278523)
            ·
              refine ⟨1405253892484249495917785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 936835928322832997278523 1405253892484249495917785)
              ·
                refine ⟨1053940419363187121938339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1405253892484249495917785 1053940419363187121938339)
                ·
                  refine ⟨1580910629044780682907509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1053940419363187121938339 1580910629044780682907509)
                  ·
                    refine ⟨148210371472948189022579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1580910629044780682907509 148210371472948189022579)
                    ·
                      rfl

theorem cell22_432958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_432958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_432958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_432958 prefixEnd_432958 := by exact prefixLift 432958
  have htrace : WordTrace (prefixWord ++ tailWord_432958) baseStart_432958 baseEnd_432958 := by
    simpa [prefixWord, tailWord_432958, baseEnd_432958] using wordTrace_append hprefix tailTrace_432958
  have hstable : (prefixWord ++ tailWord_432958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432958).length < 2 ^ (prefixWord ++ tailWord_432958).sum := by decide
  have hdescent : baseEnd_432958 < baseStart_432958 := by decide
  rcases family_descends (prefixWord ++ tailWord_432958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432977 : List Nat := [1, 2, 2, 1, 7, 1, 2, 2, 4]
def baseStart_432977 : Nat := 118140960795 + 432977 * 2 ^ 59
def prefixEnd_432977 : Nat := 4983230072969 + 3 ^ 40 * 432977 * 2
def baseEnd_432977 : Nat := 49405625187079490932507

theorem tailTrace_432977 : CollatzResearch.WordTrace tailWord_432977 prefixEnd_432977 49405625187079490932507 := by
  unfold tailWord_432977
  simp only [CollatzResearch.WordTrace]
  refine ⟨15791968552405750429521185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10527979034937166953014123 15791968552405750429521185)
  ·
    refine ⟨11843976414304312822140889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15791968552405750429521185 11843976414304312822140889)
    ·
      refine ⟨8882982310728234616605667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11843976414304312822140889 8882982310728234616605667)
      ·
        refine ⟨13324473466092351924908501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8882982310728234616605667 13324473466092351924908501)
        ·
          refine ⟨312292346861539498240043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 13324473466092351924908501 312292346861539498240043)
          ·
            refine ⟨468438520292309247360065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312292346861539498240043 468438520292309247360065)
            ·
              refine ⟨351328890219231935520049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 468438520292309247360065 351328890219231935520049)
              ·
                refine ⟨263496667664423951640037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 351328890219231935520049 263496667664423951640037)
                ·
                  refine ⟨49405625187079490932507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 263496667664423951640037 49405625187079490932507)
                  ·
                    rfl

theorem cell22_432977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 2, 2, 4].length) (baseStart_432977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_432977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_432977 prefixEnd_432977 := by exact prefixLift 432977
  have htrace : WordTrace (prefixWord ++ tailWord_432977) baseStart_432977 baseEnd_432977 := by
    simpa [prefixWord, tailWord_432977, baseEnd_432977] using wordTrace_append hprefix tailTrace_432977
  have hstable : (prefixWord ++ tailWord_432977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432977).length < 2 ^ (prefixWord ++ tailWord_432977).sum := by decide
  have hdescent : baseEnd_432977 < baseStart_432977 := by decide
  rcases family_descends (prefixWord ++ tailWord_432977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432988 : List Nat := [2, 2, 4, 2, 1, 3, 1, 7]
def baseStart_432988 : Nat := 118140960795 + 432988 * 2 ^ 59
def prefixEnd_432988 : Nat := 4983230072969 + 3 ^ 40 * 432988 * 2
def baseEnd_432988 : Nat := 16468960120670901196943

theorem tailTrace_432988 : CollatzResearch.WordTrace tailWord_432988 prefixEnd_432988 16468960120670901196943 := by
  unfold tailWord_432988
  simp only [CollatzResearch.WordTrace]
  refine ⟨7896184877682949654085809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10528246503577266205447745 7896184877682949654085809)
  ·
    refine ⟨5922138658262212240564357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7896184877682949654085809 5922138658262212240564357)
    ·
      refine ⟨1110400998424164795105817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5922138658262212240564357 1110400998424164795105817)
      ·
        refine ⟨832800748818123596329363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1110400998424164795105817 832800748818123596329363)
        ·
          refine ⟨1249201123227185394494045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 832800748818123596329363 1249201123227185394494045)
          ·
            refine ⟨468450421210194522935267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1249201123227185394494045 468450421210194522935267)
            ·
              refine ⟨702675631815291784402901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 468450421210194522935267 702675631815291784402901)
              ·
                refine ⟨16468960120670901196943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 702675631815291784402901 16468960120670901196943)
                ·
                  rfl

theorem cell22_432988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 7].length) (baseStart_432988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_432988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_432988 prefixEnd_432988 := by exact prefixLift 432988
  have htrace : WordTrace (prefixWord ++ tailWord_432988) baseStart_432988 baseEnd_432988 := by
    simpa [prefixWord, tailWord_432988, baseEnd_432988] using wordTrace_append hprefix tailTrace_432988
  have hstable : (prefixWord ++ tailWord_432988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432988).length < 2 ^ (prefixWord ++ tailWord_432988).sum := by decide
  have hdescent : baseEnd_432988 < baseStart_432988 := by decide
  rcases family_descends (prefixWord ++ tailWord_432988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433026 : List Nat := [3, 4, 2, 2, 2, 1, 1, 2, 2, 3]
def baseStart_433026 : Nat := 118140960795 + 433026 * 2 ^ 59
def prefixEnd_433026 : Nat := 4983230072969 + 3 ^ 40 * 433026 * 2
def baseEnd_433026 : Nat := 148233649262618678322371

theorem tailTrace_433026 : CollatzResearch.WordTrace tailWord_433026 prefixEnd_433026 148233649262618678322371 := by
  unfold tailWord_433026
  simp only [CollatzResearch.WordTrace]
  refine ⟨3948438932307057949513733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10529170486152154532036621 3948438932307057949513733)
  ·
    refine ⟨740332299807573365533825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3948438932307057949513733 740332299807573365533825)
    ·
      refine ⟨555249224855680024150369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 740332299807573365533825 555249224855680024150369)
      ·
        refine ⟨416436918641760018112777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 555249224855680024150369 416436918641760018112777)
        ·
          refine ⟨312327688981320013584583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 416436918641760018112777 312327688981320013584583)
          ·
            refine ⟨468491533471980020376875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312327688981320013584583 468491533471980020376875)
            ·
              refine ⟨702737300207970030565313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 468491533471980020376875 702737300207970030565313)
              ·
                refine ⟨527052975155977522923985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 702737300207970030565313 527052975155977522923985)
                ·
                  refine ⟨395289731366983142192989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 527052975155977522923985 395289731366983142192989)
                  ·
                    refine ⟨148233649262618678322371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 395289731366983142192989 148233649262618678322371)
                    ·
                      rfl

theorem cell22_433026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_433026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_433026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_433026 prefixEnd_433026 := by exact prefixLift 433026
  have htrace : WordTrace (prefixWord ++ tailWord_433026) baseStart_433026 baseEnd_433026 := by
    simpa [prefixWord, tailWord_433026, baseEnd_433026] using wordTrace_append hprefix tailTrace_433026
  have hstable : (prefixWord ++ tailWord_433026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433026).length < 2 ^ (prefixWord ++ tailWord_433026).sum := by decide
  have hdescent : baseEnd_433026 < baseStart_433026 := by decide
  rcases family_descends (prefixWord ++ tailWord_433026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433031 : List Nat := [1, 1, 4, 2, 3, 1, 1, 2, 2, 5]
def baseStart_433031 : Nat := 118140960795 + 433031 * 2 ^ 59
def prefixEnd_433031 : Nat := 4983230072969 + 3 ^ 40 * 433031 * 2
def baseEnd_433031 : Nat := 148235360864800331947355

theorem tailTrace_433031 : CollatzResearch.WordTrace tailWord_433031 prefixEnd_433031 148235360864800331947355 := by
  unfold tailWord_433031
  simp only [CollatzResearch.WordTrace]
  refine ⟨15793938094210117651986947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10529292062806745101324631 15793938094210117651986947)
  ·
    refine ⟨23690907141315176477980421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15793938094210117651986947 23690907141315176477980421)
    ·
      refine ⟨4442045088996595589621329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23690907141315176477980421 4442045088996595589621329)
      ·
        refine ⟨3331533816747446692215997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4442045088996595589621329 3331533816747446692215997)
        ·
          refine ⟨1249325181280292509580999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3331533816747446692215997 1249325181280292509580999)
          ·
            refine ⟨1873987771920438764371499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1249325181280292509580999 1873987771920438764371499)
            ·
              refine ⟨2810981657880658146557249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1873987771920438764371499 2810981657880658146557249)
              ·
                refine ⟨2108236243410493609917937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2810981657880658146557249 2108236243410493609917937)
                ·
                  refine ⟨1581177182557870207438453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2108236243410493609917937 1581177182557870207438453)
                  ·
                    refine ⟨148235360864800331947355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1581177182557870207438453 148235360864800331947355)
                    ·
                      rfl

theorem cell22_433031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_433031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_433031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_433031 prefixEnd_433031 := by exact prefixLift 433031
  have htrace : WordTrace (prefixWord ++ tailWord_433031) baseStart_433031 baseEnd_433031 := by
    simpa [prefixWord, tailWord_433031, baseEnd_433031] using wordTrace_append hprefix tailTrace_433031
  have hstable : (prefixWord ++ tailWord_433031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433031).length < 2 ^ (prefixWord ++ tailWord_433031).sum := by decide
  have hdescent : baseEnd_433031 < baseStart_433031 := by decide
  rcases family_descends (prefixWord ++ tailWord_433031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433033 : List Nat := [1, 2, 1, 1, 5, 4, 1, 2, 5]
def baseStart_433033 : Nat := 118140960795 + 433033 * 2 ^ 59
def prefixEnd_433033 : Nat := 4983230072969 + 3 ^ 40 * 433033 * 2
def baseEnd_433033 : Nat := 49412015168557664465783

theorem tailTrace_433033 : CollatzResearch.WordTrace tailWord_433033 prefixEnd_433033 49412015168557664465783 := by
  unfold tailWord_433033
  simp only [CollatzResearch.WordTrace]
  refine ⟨15794011040202871993559753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10529340693468581329039835 15794011040202871993559753)
  ·
    refine ⟨11845508280152153995169815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15794011040202871993559753 11845508280152153995169815)
    ·
      refine ⟨17768262420228230992754723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11845508280152153995169815 17768262420228230992754723)
      ·
        refine ⟨26652393630342346489132085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17768262420228230992754723 26652393630342346489132085)
        ·
          refine ⟨2498661902844594983356133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26652393630342346489132085 2498661902844594983356133)
          ·
            refine ⟨468499106783361559379275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2498661902844594983356133 468499106783361559379275)
            ·
              refine ⟨702748660175042339068913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 468499106783361559379275 702748660175042339068913)
              ·
                refine ⟨527061495131281754301685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 702748660175042339068913 527061495131281754301685)
                ·
                  refine ⟨49412015168557664465783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 527061495131281754301685 49412015168557664465783)
                  ·
                    rfl

theorem cell22_433033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 2, 5].length) (baseStart_433033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_433033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_433033 prefixEnd_433033 := by exact prefixLift 433033
  have htrace : WordTrace (prefixWord ++ tailWord_433033) baseStart_433033 baseEnd_433033 := by
    simpa [prefixWord, tailWord_433033, baseEnd_433033] using wordTrace_append hprefix tailTrace_433033
  have hstable : (prefixWord ++ tailWord_433033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433033).length < 2 ^ (prefixWord ++ tailWord_433033).sum := by decide
  have hdescent : baseEnd_433033 < baseStart_433033 := by decide
  rcases family_descends (prefixWord ++ tailWord_433033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433050 : List Nat := [3, 1, 1, 4, 3, 1, 3, 1, 5]
def baseStart_433050 : Nat := 118140960795 + 433050 * 2 ^ 59
def prefixEnd_433050 : Nat := 4983230072969 + 3 ^ 40 * 433050 * 2
def baseEnd_433050 : Nat := 49413954984363538574099

theorem tailTrace_433050 : CollatzResearch.WordTrace tailWord_433050 prefixEnd_433050 49413954984363538574099 := by
  unfold tailWord_433050
  simp only [CollatzResearch.WordTrace]
  refine ⟨3948657770285320974232151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10529754054094189264619069 3948657770285320974232151)
  ·
    refine ⟨5922986655427981461348227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3948657770285320974232151 5922986655427981461348227)
    ·
      refine ⟨8884479983141972192022341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5922986655427981461348227 8884479983141972192022341)
      ·
        refine ⟨1665839996839119786004189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8884479983141972192022341 1665839996839119786004189)
        ·
          refine ⟨624689998814669919751571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1665839996839119786004189 624689998814669919751571)
          ·
            refine ⟨937034998222004879627357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 624689998814669919751571 937034998222004879627357)
            ·
              refine ⟨351388124333251829860259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 937034998222004879627357 351388124333251829860259)
              ·
                refine ⟨527082186499877744790389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 351388124333251829860259 527082186499877744790389)
                ·
                  refine ⟨49413954984363538574099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 527082186499877744790389 49413954984363538574099)
                  ·
                    rfl

theorem cell22_433050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3, 1, 5].length) (baseStart_433050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_433050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_433050 prefixEnd_433050 := by exact prefixLift 433050
  have htrace : WordTrace (prefixWord ++ tailWord_433050) baseStart_433050 baseEnd_433050 := by
    simpa [prefixWord, tailWord_433050, baseEnd_433050] using wordTrace_append hprefix tailTrace_433050
  have hstable : (prefixWord ++ tailWord_433050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433050).length < 2 ^ (prefixWord ++ tailWord_433050).sum := by decide
  have hdescent : baseEnd_433050 < baseStart_433050 := by decide
  rcases family_descends (prefixWord ++ tailWord_433050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433091 : List Nat := [1, 1, 1, 3, 1, 1, 2, 6, 2, 4]
def baseStart_433091 : Nat := 118140960795 + 433091 * 2 ^ 59
def prefixEnd_433091 : Nat := 4983230072969 + 3 ^ 40 * 433091 * 2
def baseEnd_433091 : Nat := 148255900090980175447171

theorem tailTrace_433091 : CollatzResearch.WordTrace tailWord_433091 prefixEnd_433091 148255900090980175447171 := by
  unfold tailWord_433091
  simp only [CollatzResearch.WordTrace]
  refine ⟨15796126473992747899171127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10530750982661831932780751 15796126473992747899171127)
  ·
    refine ⟨23694189710989121848756691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15796126473992747899171127 23694189710989121848756691)
    ·
      refine ⟨35541284566483682773135037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23694189710989121848756691 35541284566483682773135037)
      ·
        refine ⟨13327981712431381039925639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35541284566483682773135037 13327981712431381039925639)
        ·
          refine ⟨19991972568647071559888459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13327981712431381039925639 19991972568647071559888459)
          ·
            refine ⟨29987958852970607339832689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19991972568647071559888459 29987958852970607339832689)
            ·
              refine ⟨22490969139727955504874517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29987958852970607339832689 22490969139727955504874517)
              ·
                refine ⟨1054264178424747914290993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22490969139727955504874517 1054264178424747914290993)
                ·
                  refine ⟨790698133818560935718245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1054264178424747914290993 790698133818560935718245)
                  ·
                    refine ⟨148255900090980175447171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 790698133818560935718245 148255900090980175447171)
                    ·
                      rfl

theorem cell22_433091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6, 2, 4].length) (baseStart_433091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_433091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_433091 prefixEnd_433091 := by exact prefixLift 433091
  have htrace : WordTrace (prefixWord ++ tailWord_433091) baseStart_433091 baseEnd_433091 := by
    simpa [prefixWord, tailWord_433091, baseEnd_433091] using wordTrace_append hprefix tailTrace_433091
  have hstable : (prefixWord ++ tailWord_433091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433091).length < 2 ^ (prefixWord ++ tailWord_433091).sum := by decide
  have hdescent : baseEnd_433091 < baseStart_433091 := by decide
  rcases family_descends (prefixWord ++ tailWord_433091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433101 : List Nat := [1, 6, 3, 1, 1, 2, 2, 1, 5]
def baseStart_433101 : Nat := 118140960795 + 433101 * 2 ^ 59
def prefixEnd_433101 : Nat := 4983230072969 + 3 ^ 40 * 433101 * 2
def baseEnd_433101 : Nat := 49419774431781160899047

theorem tailTrace_433101 : CollatzResearch.WordTrace tailWord_433101 prefixEnd_433101 49419774431781160899047 := by
  unfold tailWord_433101
  simp only [CollatzResearch.WordTrace]
  refine ⟨15796491203956519607035157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10530994135971013071356771 15796491203956519607035157)
  ·
    refine ⟨740460525185461856579773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15796491203956519607035157 740460525185461856579773)
    ·
      refine ⟨277672696944548196217415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 740460525185461856579773 277672696944548196217415)
      ·
        refine ⟨416509045416822294326123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277672696944548196217415 416509045416822294326123)
        ·
          refine ⟨624763568125233441489185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 416509045416822294326123 624763568125233441489185)
          ·
            refine ⟨468572676093925081116889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 624763568125233441489185 468572676093925081116889)
            ·
              refine ⟨351429507070443810837667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 468572676093925081116889 351429507070443810837667)
              ·
                refine ⟨527144260605665716256501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 351429507070443810837667 527144260605665716256501)
                ·
                  refine ⟨49419774431781160899047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 527144260605665716256501 49419774431781160899047)
                  ·
                    rfl

theorem cell22_433101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_433101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_433101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_433101 prefixEnd_433101 := by exact prefixLift 433101
  have htrace : WordTrace (prefixWord ++ tailWord_433101) baseStart_433101 baseEnd_433101 := by
    simpa [prefixWord, tailWord_433101, baseEnd_433101] using wordTrace_append hprefix tailTrace_433101
  have hstable : (prefixWord ++ tailWord_433101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433101).length < 2 ^ (prefixWord ++ tailWord_433101).sum := by decide
  have hdescent : baseEnd_433101 < baseStart_433101 := by decide
  rcases family_descends (prefixWord ++ tailWord_433101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433196 : List Nat := [2, 2, 1, 1, 1, 2, 3, 2, 8]
def baseStart_433196 : Nat := 118140960795 + 433196 * 2 ^ 59
def prefixEnd_433196 : Nat := 4983230072969 + 3 ^ 40 * 433196 * 2
def baseEnd_433196 : Nat := 49430614578931633857283

theorem tailTrace_433196 : CollatzResearch.WordTrace tailWord_433196 prefixEnd_433196 49430614578931633857283 := by
  unfold tailWord_433196
  simp only [CollatzResearch.WordTrace]
  refine ⟨7899978069306175415871721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10533304092408233887828961 7899978069306175415871721)
  ·
    refine ⟨5924983551979631561903791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7899978069306175415871721 5924983551979631561903791)
    ·
      refine ⟨8887475327969447342855687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5924983551979631561903791 8887475327969447342855687)
      ·
        refine ⟨13331212991954171014283531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8887475327969447342855687 13331212991954171014283531)
        ·
          refine ⟨19996819487931256521425297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13331212991954171014283531 19996819487931256521425297)
          ·
            refine ⟨14997614615948442391068973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19996819487931256521425297 14997614615948442391068973)
            ·
              refine ⟨5624105480980665896650865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14997614615948442391068973 5624105480980665896650865)
              ·
                refine ⟨4218079110735499422488149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5624105480980665896650865 4218079110735499422488149)
                ·
                  refine ⟨49430614578931633857283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4218079110735499422488149 49430614578931633857283)
                  ·
                    rfl

theorem cell22_433196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 8].length) (baseStart_433196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_433196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_433196 prefixEnd_433196 := by exact prefixLift 433196
  have htrace : WordTrace (prefixWord ++ tailWord_433196) baseStart_433196 baseEnd_433196 := by
    simpa [prefixWord, tailWord_433196, baseEnd_433196] using wordTrace_append hprefix tailTrace_433196
  have hstable : (prefixWord ++ tailWord_433196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433196).length < 2 ^ (prefixWord ++ tailWord_433196).sum := by decide
  have hdescent : baseEnd_433196 < baseStart_433196 := by decide
  rcases family_descends (prefixWord ++ tailWord_433196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433213 : List Nat := [1, 4, 1, 3, 1, 2, 1, 3, 6]
def baseStart_433213 : Nat := 118140960795 + 433213 * 2 ^ 59
def prefixEnd_433213 : Nat := 4983230072969 + 3 ^ 40 * 433213 * 2
def baseEnd_433213 : Nat := 49432554394737507965599

theorem tailTrace_433213 : CollatzResearch.WordTrace tailWord_433213 prefixEnd_433213 49432554394737507965599 := by
  unfold tailWord_433213
  simp only [CollatzResearch.WordTrace]
  refine ⟨15800576179550762735112293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10533717453033841823408195 15800576179550762735112293)
  ·
    refine ⟨2962608033665768012833555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15800576179550762735112293 2962608033665768012833555)
    ·
      refine ⟨4443912050498652019250333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2962608033665768012833555 4443912050498652019250333)
      ·
        refine ⟨1666467018936994507218875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4443912050498652019250333 1666467018936994507218875)
        ·
          refine ⟨2499700528405491760828313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1666467018936994507218875 2499700528405491760828313)
          ·
            refine ⟨1874775396304118820621235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2499700528405491760828313 1874775396304118820621235)
            ·
              refine ⟨2812163094456178230931853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1874775396304118820621235 2812163094456178230931853)
              ·
                refine ⟨1054561160421066836599445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2812163094456178230931853 1054561160421066836599445)
                ·
                  refine ⟨49432554394737507965599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1054561160421066836599445 49432554394737507965599)
                  ·
                    rfl

theorem cell22_433213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 3, 6].length) (baseStart_433213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_433213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_433213 prefixEnd_433213 := by exact prefixLift 433213
  have htrace : WordTrace (prefixWord ++ tailWord_433213) baseStart_433213 baseEnd_433213 := by
    simpa [prefixWord, tailWord_433213, baseEnd_433213] using wordTrace_append hprefix tailTrace_433213
  have hstable : (prefixWord ++ tailWord_433213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433213).length < 2 ^ (prefixWord ++ tailWord_433213).sum := by decide
  have hdescent : baseEnd_433213 < baseStart_433213 := by decide
  rcases family_descends (prefixWord ++ tailWord_433213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433258 : List Nat := [3, 1, 3, 2, 2, 1, 10]
def baseStart_433258 : Nat := 118140960795 + 433258 * 2 ^ 59
def prefixEnd_433258 : Nat := 4983230072969 + 3 ^ 40 * 433258 * 2
def baseEnd_433258 : Nat := 5493076577920274315617

theorem tailTrace_433258 : CollatzResearch.WordTrace tailWord_433258 prefixEnd_433258 5493076577920274315617 := by
  unfold tailWord_433258
  simp only [CollatzResearch.WordTrace]
  refine ⟨3950554366096933855125107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10534811642925156947000285 3950554366096933855125107)
  ·
    refine ⟨5925831549145400782687661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3950554366096933855125107 5925831549145400782687661)
    ·
      refine ⟨2222186830929525293507873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5925831549145400782687661 2222186830929525293507873)
      ·
        refine ⟨1666640123197143970130905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2222186830929525293507873 1666640123197143970130905)
        ·
          refine ⟨1249980092397857977598179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1666640123197143970130905 1249980092397857977598179)
          ·
            refine ⟨1874970138596786966397269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1249980092397857977598179 1874970138596786966397269)
            ·
              refine ⟨5493076577920274315617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1874970138596786966397269 5493076577920274315617)
              ·
                rfl

theorem cell22_433258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 10].length) (baseStart_433258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_433258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_433258 prefixEnd_433258 := by exact prefixLift 433258
  have htrace : WordTrace (prefixWord ++ tailWord_433258) baseStart_433258 baseEnd_433258 := by
    simpa [prefixWord, tailWord_433258, baseEnd_433258] using wordTrace_append hprefix tailTrace_433258
  have hstable : (prefixWord ++ tailWord_433258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433258).length < 2 ^ (prefixWord ++ tailWord_433258).sum := by decide
  have hdescent : baseEnd_433258 < baseStart_433258 := by decide
  rcases family_descends (prefixWord ++ tailWord_433258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433290 : List Nat := [3, 1, 2, 3, 1, 1, 2, 1, 5, 3]
def baseStart_433290 : Nat := 118140960795 + 433290 * 2 ^ 59
def prefixEnd_433290 : Nat := 4983230072969 + 3 ^ 40 * 433290 * 2
def baseEnd_433290 : Nat := 148324021857809989721561

theorem tailTrace_433290 : CollatzResearch.WordTrace tailWord_433290 prefixEnd_433290 148324021857809989721561 := by
  unfold tailWord_433290
  simp only [CollatzResearch.WordTrace]
  refine ⟨3950846150067951221416331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10535589733514536590443549 3950846150067951221416331)
  ·
    refine ⟨5926269225101926832124497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3950846150067951221416331 5926269225101926832124497)
    ·
      refine ⟨4444701918826445124093373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5926269225101926832124497 4444701918826445124093373)
      ·
        refine ⟨1666763219559916921535015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4444701918826445124093373 1666763219559916921535015)
        ·
          refine ⟨2500144829339875382302523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1666763219559916921535015 2500144829339875382302523)
          ·
            refine ⟨3750217244009813073453785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2500144829339875382302523 3750217244009813073453785)
            ·
              refine ⟨2812662933007359805090339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3750217244009813073453785 2812662933007359805090339)
              ·
                refine ⟨4218994399511039707635509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2812662933007359805090339 4218994399511039707635509)
                ·
                  refine ⟨395530724954159972590829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4218994399511039707635509 395530724954159972590829)
                  ·
                    refine ⟨148324021857809989721561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 395530724954159972590829 148324021857809989721561)
                    ·
                      rfl

theorem cell22_433290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 5, 3].length) (baseStart_433290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_433290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_433290 prefixEnd_433290 := by exact prefixLift 433290
  have htrace : WordTrace (prefixWord ++ tailWord_433290) baseStart_433290 baseEnd_433290 := by
    simpa [prefixWord, tailWord_433290, baseEnd_433290] using wordTrace_append hprefix tailTrace_433290
  have hstable : (prefixWord ++ tailWord_433290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433290).length < 2 ^ (prefixWord ++ tailWord_433290).sum := by decide
  have hdescent : baseEnd_433290 < baseStart_433290 := by decide
  rcases family_descends (prefixWord ++ tailWord_433290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433367 : List Nat := [1, 1, 3, 2, 1, 2, 6, 1, 1, 4]
def baseStart_433367 : Nat := 118140960795 + 433367 * 2 ^ 59
def prefixEnd_433367 : Nat := 4983230072969 + 3 ^ 40 * 433367 * 2
def baseEnd_433367 : Nat := 148350380531407455546325

theorem tailTrace_433367 : CollatzResearch.WordTrace tailWord_433367 prefixEnd_433367 148350380531407455546325 := by
  unfold tailWord_433367
  simp only [CollatzResearch.WordTrace]
  refine ⟨15806193020992847036218355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10537462013995231357478903 15806193020992847036218355)
  ·
    refine ⟨23709289531489270554327533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15806193020992847036218355 23709289531489270554327533)
    ·
      refine ⟨8890983574308476457872825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23709289531489270554327533 8890983574308476457872825)
      ·
        refine ⟨6668237680731357343404619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8890983574308476457872825 6668237680731357343404619)
        ·
          refine ⟨10002356521097036015106929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6668237680731357343404619 10002356521097036015106929)
          ·
            refine ⟨7501767390822777011330197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10002356521097036015106929 7501767390822777011330197)
            ·
              refine ⟨351645346444817672406103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7501767390822777011330197 351645346444817672406103)
              ·
                refine ⟨527468019667226508609155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 351645346444817672406103 527468019667226508609155)
                ·
                  refine ⟨791202029500839762913733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 527468019667226508609155 791202029500839762913733)
                  ·
                    refine ⟨148350380531407455546325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 791202029500839762913733 148350380531407455546325)
                    ·
                      rfl

theorem cell22_433367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6, 1, 1, 4].length) (baseStart_433367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_433367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_433367 prefixEnd_433367 := by exact prefixLift 433367
  have htrace : WordTrace (prefixWord ++ tailWord_433367) baseStart_433367 baseEnd_433367 := by
    simpa [prefixWord, tailWord_433367, baseEnd_433367] using wordTrace_append hprefix tailTrace_433367
  have hstable : (prefixWord ++ tailWord_433367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433367).length < 2 ^ (prefixWord ++ tailWord_433367).sum := by decide
  have hdescent : baseEnd_433367 < baseStart_433367 := by decide
  rcases family_descends (prefixWord ++ tailWord_433367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433393 : List Nat := [1, 2, 2, 2, 2, 1, 1, 11]
def baseStart_433393 : Nat := 118140960795 + 433393 * 2 ^ 59
def prefixEnd_433393 : Nat := 4983230072969 + 3 ^ 40 * 433393 * 2
def baseEnd_433393 : Nat := 16484364540305783821805

theorem tailTrace_433393 : CollatzResearch.WordTrace tailWord_433393 prefixEnd_433393 16484364540305783821805 := by
  unfold tailWord_433393
  simp only [CollatzResearch.WordTrace]
  refine ⟨15807141318898653476664833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10538094212599102317776555 15807141318898653476664833)
  ·
    refine ⟨11855355989173990107498625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15807141318898653476664833 11855355989173990107498625)
    ·
      refine ⟨8891516991880492580623969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11855355989173990107498625 8891516991880492580623969)
      ·
        refine ⟨6668637743910369435467977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8891516991880492580623969 6668637743910369435467977)
        ·
          refine ⟨5001478307932777076600983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6668637743910369435467977 5001478307932777076600983)
          ·
            refine ⟨7502217461899165614901475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5001478307932777076600983 7502217461899165614901475)
            ·
              refine ⟨11253326192848748422352213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7502217461899165614901475 11253326192848748422352213)
              ·
                refine ⟨16484364540305783821805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 11253326192848748422352213 16484364540305783821805)
                ·
                  rfl

theorem cell22_433393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 11].length) (baseStart_433393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_433393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_433393 prefixEnd_433393 := by exact prefixLift 433393
  have htrace : WordTrace (prefixWord ++ tailWord_433393) baseStart_433393 baseEnd_433393 := by
    simpa [prefixWord, tailWord_433393, baseEnd_433393] using wordTrace_append hprefix tailTrace_433393
  have hstable : (prefixWord ++ tailWord_433393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433393).length < 2 ^ (prefixWord ++ tailWord_433393).sum := by decide
  have hdescent : baseEnd_433393 < baseStart_433393 := by decide
  rcases family_descends (prefixWord ++ tailWord_433393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433408 : List Nat := [2, 1, 1, 2, 1, 1, 3, 1, 1, 9]
def baseStart_433408 : Nat := 118140960795 + 433408 * 2 ^ 59
def prefixEnd_433408 : Nat := 4983230072969 + 3 ^ 40 * 433408 * 2
def baseEnd_433408 : Nat := 148364415669297015271199

theorem tailTrace_433408 : CollatzResearch.WordTrace tailWord_433408 prefixEnd_433408 148364415669297015271199 := by
  unfold tailWord_433408
  simp only [CollatzResearch.WordTrace]
  refine ⟨7903844206922155519230439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10538458942562874025640585 7903844206922155519230439)
  ·
    refine ⟨11855766310383233278845659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7903844206922155519230439 11855766310383233278845659)
    ·
      refine ⟨17783649465574849918268489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11855766310383233278845659 17783649465574849918268489)
      ·
        refine ⟨13337737099181137438701367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17783649465574849918268489 13337737099181137438701367)
        ·
          refine ⟨20006605648771706158052051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13337737099181137438701367 20006605648771706158052051)
          ·
            refine ⟨30009908473157559237078077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20006605648771706158052051 30009908473157559237078077)
            ·
              refine ⟨11253715677434084713904279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30009908473157559237078077 11253715677434084713904279)
              ·
                refine ⟨16880573516151127070856419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11253715677434084713904279 16880573516151127070856419)
                ·
                  refine ⟨25320860274226690606284629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16880573516151127070856419 25320860274226690606284629)
                  ·
                    refine ⟨148364415669297015271199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 25320860274226690606284629 148364415669297015271199)
                    ·
                      rfl

theorem cell22_433408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 1, 9].length) (baseStart_433408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_433408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_433408 prefixEnd_433408 := by exact prefixLift 433408
  have htrace : WordTrace (prefixWord ++ tailWord_433408) baseStart_433408 baseEnd_433408 := by
    simpa [prefixWord, tailWord_433408, baseEnd_433408] using wordTrace_append hprefix tailTrace_433408
  have hstable : (prefixWord ++ tailWord_433408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433408).length < 2 ^ (prefixWord ++ tailWord_433408).sum := by decide
  have hdescent : baseEnd_433408 < baseStart_433408 := by decide
  rcases family_descends (prefixWord ++ tailWord_433408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433416 : List Nat := [2, 1, 3, 2, 5, 1, 1, 3, 4]
def baseStart_433416 : Nat := 118140960795 + 433416 * 2 ^ 59
def prefixEnd_433416 : Nat := 4983230072969 + 3 ^ 40 * 433416 * 2
def baseEnd_433416 : Nat := 49455718077595887023725

theorem tailTrace_433416 : CollatzResearch.WordTrace tailWord_433416 prefixEnd_433416 49455718077595887023725 := by
  unfold tailWord_433416
  simp only [CollatzResearch.WordTrace]
  refine ⟨7903990098907664202376051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10538653465210218936501401 7903990098907664202376051)
  ·
    refine ⟨11855985148361496303564077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7903990098907664202376051 11855985148361496303564077)
    ·
      refine ⟨4445994430635561113836529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11855985148361496303564077 4445994430635561113836529)
      ·
        refine ⟨3334495822976670835377397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4445994430635561113836529 3334495822976670835377397)
        ·
          refine ⟨312608983404062890816631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3334495822976670835377397 312608983404062890816631)
          ·
            refine ⟨468913475106094336224947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312608983404062890816631 468913475106094336224947)
            ·
              refine ⟨703370212659141504337421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 468913475106094336224947 703370212659141504337421)
              ·
                refine ⟨263763829747178064126533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 703370212659141504337421 263763829747178064126533)
                ·
                  refine ⟨49455718077595887023725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 263763829747178064126533 49455718077595887023725)
                  ·
                    rfl

theorem cell22_433416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 3, 4].length) (baseStart_433416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_433416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_433416 prefixEnd_433416 := by exact prefixLift 433416
  have htrace : WordTrace (prefixWord ++ tailWord_433416) baseStart_433416 baseEnd_433416 := by
    simpa [prefixWord, tailWord_433416, baseEnd_433416] using wordTrace_append hprefix tailTrace_433416
  have hstable : (prefixWord ++ tailWord_433416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433416).length < 2 ^ (prefixWord ++ tailWord_433416).sum := by decide
  have hdescent : baseEnd_433416 < baseStart_433416 := by decide
  rcases family_descends (prefixWord ++ tailWord_433416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433423 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 3, 8]
def baseStart_433423 : Nat := 118140960795 + 433423 * 2 ^ 59
def prefixEnd_433423 : Nat := 4983230072969 + 3 ^ 40 * 433423 * 2
def baseEnd_433423 : Nat := 148369550475841976146153

theorem tailTrace_433423 : CollatzResearch.WordTrace tailWord_433423 prefixEnd_433423 148369550475841976146153 := by
  unfold tailWord_433423
  simp only [CollatzResearch.WordTrace]
  refine ⟨15808235508789968600256923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10538823672526645733504615 15808235508789968600256923)
  ·
    refine ⟨23712353263184952900385385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15808235508789968600256923 23712353263184952900385385)
    ·
      refine ⟨17784264947388714675289039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23712353263184952900385385 17784264947388714675289039)
      ·
        refine ⟨26676397421083072012933559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17784264947388714675289039 26676397421083072012933559)
        ·
          refine ⟨40014596131624608019400339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26676397421083072012933559 40014596131624608019400339)
          ·
            refine ⟨60021894197436912029100509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40014596131624608019400339 60021894197436912029100509)
            ·
              refine ⟨22508210324038842010912691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60021894197436912029100509 22508210324038842010912691)
              ·
                refine ⟨33762315486058263016369037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22508210324038842010912691 33762315486058263016369037)
                ·
                  refine ⟨12660868307271848631138389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33762315486058263016369037 12660868307271848631138389)
                  ·
                    refine ⟨148369550475841976146153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 12660868307271848631138389 148369550475841976146153)
                    ·
                      rfl

theorem cell22_433423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 8].length) (baseStart_433423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_433423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_433423 prefixEnd_433423 := by exact prefixLift 433423
  have htrace : WordTrace (prefixWord ++ tailWord_433423) baseStart_433423 baseEnd_433423 := by
    simpa [prefixWord, tailWord_433423, baseEnd_433423] using wordTrace_append hprefix tailTrace_433423
  have hstable : (prefixWord ++ tailWord_433423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433423).length < 2 ^ (prefixWord ++ tailWord_433423).sum := by decide
  have hdescent : baseEnd_433423 < baseStart_433423 := by decide
  rcases family_descends (prefixWord ++ tailWord_433423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433493 : List Nat := [1, 3, 2, 2, 3, 3, 2, 2, 1, 3]
def baseStart_433493 : Nat := 118140960795 + 433493 * 2 ^ 59
def prefixEnd_433493 : Nat := 4983230072969 + 3 ^ 40 * 433493 * 2
def baseEnd_433493 : Nat := 148393512906385126895939

theorem tailTrace_433493 : CollatzResearch.WordTrace tailWord_433493 prefixEnd_433493 148393512906385126895939 := by
  unfold tailWord_433493
  simp only [CollatzResearch.WordTrace]
  refine ⟨15810788618536370555305133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10540525745690913703536755 15810788618536370555305133)
  ·
    refine ⟨5929045731951138958239425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15810788618536370555305133 5929045731951138958239425)
    ·
      refine ⟨4446784298963354218679569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5929045731951138958239425 4446784298963354218679569)
      ·
        refine ⟨3335088224222515664009677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4446784298963354218679569 3335088224222515664009677)
        ·
          refine ⟨1250658084083443374003629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3335088224222515664009677 1250658084083443374003629)
          ·
            refine ⟨468996781531291265251361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1250658084083443374003629 468996781531291265251361)
            ·
              refine ⟨351747586148468448938521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 468996781531291265251361 351747586148468448938521)
              ·
                refine ⟨263810689611351336703891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 351747586148468448938521 263810689611351336703891)
                ·
                  refine ⟨395716034417027005055837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 263810689611351336703891 395716034417027005055837)
                  ·
                    refine ⟨148393512906385126895939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 395716034417027005055837 148393512906385126895939)
                    ·
                      rfl

theorem cell22_433493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2, 2, 1, 3].length) (baseStart_433493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_433493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_433493 prefixEnd_433493 := by exact prefixLift 433493
  have htrace : WordTrace (prefixWord ++ tailWord_433493) baseStart_433493 baseEnd_433493 := by
    simpa [prefixWord, tailWord_433493, baseEnd_433493] using wordTrace_append hprefix tailTrace_433493
  have hstable : (prefixWord ++ tailWord_433493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433493).length < 2 ^ (prefixWord ++ tailWord_433493).sum := by decide
  have hdescent : baseEnd_433493 < baseStart_433493 := by decide
  rcases family_descends (prefixWord ++ tailWord_433493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433517 : List Nat := [1, 5, 1, 1, 1, 4, 1, 2, 6]
def baseStart_433517 : Nat := 118140960795 + 433517 * 2 ^ 59
def prefixEnd_433517 : Nat := 4983230072969 + 3 ^ 40 * 433517 * 2
def baseEnd_433517 : Nat := 49467242865619021431955

theorem tailTrace_433517 : CollatzResearch.WordTrace tailWord_433517 prefixEnd_433517 49467242865619021431955 := by
  unfold tailWord_433517
  simp only [CollatzResearch.WordTrace]
  refine ⟨15811663970449422654178805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10541109313632948436119203 15811663970449422654178805)
  ·
    refine ⟨1482343497229633373829263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15811663970449422654178805 1482343497229633373829263)
    ·
      refine ⟨2223515245844450060743895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1482343497229633373829263 2223515245844450060743895)
      ·
        refine ⟨3335272868766675091115843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2223515245844450060743895 3335272868766675091115843)
        ·
          refine ⟨5002909303150012636673765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3335272868766675091115843 5002909303150012636673765)
          ·
            refine ⟨938045494340627369376331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5002909303150012636673765 938045494340627369376331)
            ·
              refine ⟨1407068241510941054064497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 938045494340627369376331 1407068241510941054064497)
              ·
                refine ⟨1055301181133205790548373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1407068241510941054064497 1055301181133205790548373)
                ·
                  refine ⟨49467242865619021431955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1055301181133205790548373 49467242865619021431955)
                  ·
                    rfl

theorem cell22_433517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_433517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_433517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_433517 prefixEnd_433517 := by exact prefixLift 433517
  have htrace : WordTrace (prefixWord ++ tailWord_433517) baseStart_433517 baseEnd_433517 := by
    simpa [prefixWord, tailWord_433517, baseEnd_433517] using wordTrace_append hprefix tailTrace_433517
  have hstable : (prefixWord ++ tailWord_433517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433517).length < 2 ^ (prefixWord ++ tailWord_433517).sum := by decide
  have hdescent : baseEnd_433517 < baseStart_433517 := by decide
  rcases family_descends (prefixWord ++ tailWord_433517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433530 : List Nat := [3, 1, 1, 1, 1, 1, 2, 5, 1, 6]
def baseStart_433530 : Nat := 118140960795 + 433530 * 2 ^ 59
def prefixEnd_433530 : Nat := 4983230072969 + 3 ^ 40 * 433530 * 2
def baseEnd_433530 : Nat := 148406178762529363720825

theorem tailTrace_433530 : CollatzResearch.WordTrace tailWord_433530 prefixEnd_433530 148406178762529363720825 := by
  unfold tailWord_433530
  simp only [CollatzResearch.WordTrace]
  refine ⟨3953034529850581468600511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10541425412934883916268029 3953034529850581468600511)
  ·
    refine ⟨5929551794775872202900767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3953034529850581468600511 5929551794775872202900767)
    ·
      refine ⟨8894327692163808304351151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5929551794775872202900767 8894327692163808304351151)
      ·
        refine ⟨13341491538245712456526727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8894327692163808304351151 13341491538245712456526727)
        ·
          refine ⟨20012237307368568684790091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13341491538245712456526727 20012237307368568684790091)
          ·
            refine ⟨30018355961052853027185137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20012237307368568684790091 30018355961052853027185137)
            ·
              refine ⟨22513766970789639770388853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30018355961052853027185137 22513766970789639770388853)
              ·
                refine ⟨2110665653511528728473955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22513766970789639770388853 2110665653511528728473955)
                ·
                  refine ⟨3165998480267293092710933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2110665653511528728473955 3165998480267293092710933)
                  ·
                    refine ⟨148406178762529363720825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3165998480267293092710933 148406178762529363720825)
                    ·
                      rfl

theorem cell22_433530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 1, 6].length) (baseStart_433530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_433530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_433530 prefixEnd_433530 := by exact prefixLift 433530
  have htrace : WordTrace (prefixWord ++ tailWord_433530) baseStart_433530 baseEnd_433530 := by
    simpa [prefixWord, tailWord_433530, baseEnd_433530] using wordTrace_append hprefix tailTrace_433530
  have hstable : (prefixWord ++ tailWord_433530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433530).length < 2 ^ (prefixWord ++ tailWord_433530).sum := by decide
  have hdescent : baseEnd_433530 < baseStart_433530 := by decide
  rcases family_descends (prefixWord ++ tailWord_433530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433532 : List Nat := [2, 2, 2, 1, 1, 1, 4, 2, 4, 3]
def baseStart_433532 : Nat := 118140960795 + 433532 * 2 ^ 59
def prefixEnd_433532 : Nat := 4983230072969 + 3 ^ 40 * 433532 * 2
def baseEnd_433532 : Nat := 148406863403402025170819

theorem tailTrace_433532 : CollatzResearch.WordTrace tailWord_433532 prefixEnd_433532 148406863403402025170819 := by
  unfold tailWord_433532
  simp only [CollatzResearch.WordTrace]
  refine ⟨7906105532697540107987425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10541474043596720143983233 7906105532697540107987425)
  ·
    refine ⟨5929579149523155080990569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7906105532697540107987425 5929579149523155080990569)
    ·
      refine ⟨4447184362142366310742927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5929579149523155080990569 4447184362142366310742927)
      ·
        refine ⟨6670776543213549466114391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4447184362142366310742927 6670776543213549466114391)
        ·
          refine ⟨10006164814820324199171587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6670776543213549466114391 10006164814820324199171587)
          ·
            refine ⟨15009247222230486298757381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10006164814820324199171587 15009247222230486298757381)
            ·
              refine ⟨2814233854168216181017009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15009247222230486298757381 2814233854168216181017009)
              ·
                refine ⟨2110675390626162135762757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2814233854168216181017009 2110675390626162135762757)
                ·
                  refine ⟨395751635742405400455517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2110675390626162135762757 395751635742405400455517)
                  ·
                    refine ⟨148406863403402025170819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 395751635742405400455517 148406863403402025170819)
                    ·
                      rfl

theorem cell22_433532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 4, 3].length) (baseStart_433532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_433532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_433532 prefixEnd_433532 := by exact prefixLift 433532
  have htrace : WordTrace (prefixWord ++ tailWord_433532) baseStart_433532 baseEnd_433532 := by
    simpa [prefixWord, tailWord_433532, baseEnd_433532] using wordTrace_append hprefix tailTrace_433532
  have hstable : (prefixWord ++ tailWord_433532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433532).length < 2 ^ (prefixWord ++ tailWord_433532).sum := by decide
  have hdescent : baseEnd_433532 < baseStart_433532 := by decide
  rcases family_descends (prefixWord ++ tailWord_433532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433602 : List Nat := [3, 5, 2, 1, 2, 1, 1, 1, 6]
def baseStart_433602 : Nat := 118140960795 + 433602 * 2 ^ 59
def prefixEnd_433602 : Nat := 4983230072969 + 3 ^ 40 * 433602 * 2
def baseEnd_433602 : Nat := 49476941944648391973535

theorem tailTrace_433602 : CollatzResearch.WordTrace tailWord_433602 prefixEnd_433602 49476941944648391973535 := by
  unfold tailWord_433602
  simp only [CollatzResearch.WordTrace]
  refine ⟨3953691043785370542755765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10543176116760988114015373 3953691043785370542755765)
  ·
    refine ⟨370658535354878488383353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3953691043785370542755765 370658535354878488383353)
    ·
      refine ⟨277993901516158866287515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 370658535354878488383353 277993901516158866287515)
      ·
        refine ⟨416990852274238299431273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277993901516158866287515 416990852274238299431273)
        ·
          refine ⟨312743139205678724573455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 416990852274238299431273 312743139205678724573455)
          ·
            refine ⟨469114708808518086860183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312743139205678724573455 469114708808518086860183)
            ·
              refine ⟨703672063212777130290275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 469114708808518086860183 703672063212777130290275)
              ·
                refine ⟨1055508094819165695435413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 703672063212777130290275 1055508094819165695435413)
                ·
                  refine ⟨49476941944648391973535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1055508094819165695435413 49476941944648391973535)
                  ·
                    rfl

theorem cell22_433602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_433602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_433602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_433602 prefixEnd_433602 := by exact prefixLift 433602
  have htrace : WordTrace (prefixWord ++ tailWord_433602) baseStart_433602 baseEnd_433602 := by
    simpa [prefixWord, tailWord_433602, baseEnd_433602] using wordTrace_append hprefix tailTrace_433602
  have hstable : (prefixWord ++ tailWord_433602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433602).length < 2 ^ (prefixWord ++ tailWord_433602).sum := by decide
  have hdescent : baseEnd_433602 < baseStart_433602 := by decide
  rcases family_descends (prefixWord ++ tailWord_433602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433607 : List Nat := [1, 1, 4, 1, 1, 3, 2, 4, 5]
def baseStart_433607 : Nat := 118140960795 + 433607 * 2 ^ 59
def prefixEnd_433607 : Nat := 4983230072969 + 3 ^ 40 * 433607 * 2
def baseEnd_433607 : Nat := 49477512478708943181863

theorem tailTrace_433607 : CollatzResearch.WordTrace tailWord_433607 prefixEnd_433607 49477512478708943181863 := by
  unfold tailWord_433607
  simp only [CollatzResearch.WordTrace]
  refine ⟨15814946540123368024955075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10543297693415578683303383 15814946540123368024955075)
  ·
    refine ⟨23722419810185052037432613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15814946540123368024955075 23722419810185052037432613)
    ·
      refine ⟨4447953714409697257018615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23722419810185052037432613 4447953714409697257018615)
      ·
        refine ⟨6671930571614545885527923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4447953714409697257018615 6671930571614545885527923)
        ·
          refine ⟨10007895857421818828291885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6671930571614545885527923 10007895857421818828291885)
          ·
            refine ⟨3752960946533182060609457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10007895857421818828291885 3752960946533182060609457)
            ·
              refine ⟨2814720709899886545457093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3752960946533182060609457 2814720709899886545457093)
              ·
                refine ⟨527760133106228727273205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2814720709899886545457093 527760133106228727273205)
                ·
                  refine ⟨49477512478708943181863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 527760133106228727273205 49477512478708943181863)
                  ·
                    rfl

theorem cell22_433607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 4, 5].length) (baseStart_433607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_433607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_433607 prefixEnd_433607 := by exact prefixLift 433607
  have htrace : WordTrace (prefixWord ++ tailWord_433607) baseStart_433607 baseEnd_433607 := by
    simpa [prefixWord, tailWord_433607, baseEnd_433607] using wordTrace_append hprefix tailTrace_433607
  have hstable : (prefixWord ++ tailWord_433607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433607).length < 2 ^ (prefixWord ++ tailWord_433607).sum := by decide
  have hdescent : baseEnd_433607 < baseStart_433607 := by decide
  rcases family_descends (prefixWord ++ tailWord_433607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433624 : List Nat := [2, 1, 2, 2, 2, 1, 6, 1, 5]
def baseStart_433624 : Nat := 118140960795 + 433624 * 2 ^ 59
def prefixEnd_433624 : Nat := 4983230072969 + 3 ^ 40 * 433624 * 2
def baseEnd_433624 : Nat := 49479452294514817290179

theorem tailTrace_433624 : CollatzResearch.WordTrace tailWord_433624 prefixEnd_433624 49479452294514817290179 := by
  unfold tailWord_433624
  simp only [CollatzResearch.WordTrace]
  refine ⟨7907783290530889964161963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10543711054041186618882617 7907783290530889964161963)
  ·
    refine ⟨11861674935796334946242945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7907783290530889964161963 11861674935796334946242945)
    ·
      refine ⟨8896256201847251209682209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11861674935796334946242945 8896256201847251209682209)
      ·
        refine ⟨6672192151385438407261657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8896256201847251209682209 6672192151385438407261657)
        ·
          refine ⟨5004144113539078805446243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6672192151385438407261657 5004144113539078805446243)
          ·
            refine ⟨7506216170308618208169365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5004144113539078805446243 7506216170308618208169365)
            ·
              refine ⟨351853882983216478507939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7506216170308618208169365 351853882983216478507939)
              ·
                refine ⟨527780824474824717761909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 351853882983216478507939 527780824474824717761909)
                ·
                  refine ⟨49479452294514817290179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 527780824474824717761909 49479452294514817290179)
                  ·
                    rfl

theorem cell22_433624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6, 1, 5].length) (baseStart_433624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_433624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_433624 prefixEnd_433624 := by exact prefixLift 433624
  have htrace : WordTrace (prefixWord ++ tailWord_433624) baseStart_433624 baseEnd_433624 := by
    simpa [prefixWord, tailWord_433624, baseEnd_433624] using wordTrace_append hprefix tailTrace_433624
  have hstable : (prefixWord ++ tailWord_433624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433624).length < 2 ^ (prefixWord ++ tailWord_433624).sum := by decide
  have hdescent : baseEnd_433624 < baseStart_433624 := by decide
  rcases family_descends (prefixWord ++ tailWord_433624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433699 : List Nat := [1, 1, 1, 4, 5, 1, 1, 1, 1, 6]
def baseStart_433699 : Nat := 118140960795 + 433699 * 2 ^ 59
def prefixEnd_433699 : Nat := 4983230072969 + 3 ^ 40 * 433699 * 2
def baseEnd_433699 : Nat := 148464030916269256245307

theorem tailTrace_433699 : CollatzResearch.WordTrace tailWord_433699 prefixEnd_433699 148464030916269256245307 := by
  unfold tailWord_433699
  simp only [CollatzResearch.WordTrace]
  refine ⟨15818302055790067737304151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10545534703860045158202767 15818302055790067737304151)
  ·
    refine ⟨23727453083685101605956227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15818302055790067737304151 23727453083685101605956227)
    ·
      refine ⟨35591179625527652408934341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23727453083685101605956227 35591179625527652408934341)
      ·
        refine ⟨6673346179786434826675189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35591179625527652408934341 6673346179786434826675189)
        ·
          refine ⟨625626204354978265000799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6673346179786434826675189 625626204354978265000799)
          ·
            refine ⟨938439306532467397501199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 625626204354978265000799 938439306532467397501199)
            ·
              refine ⟨1407658959798701096251799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 938439306532467397501199 1407658959798701096251799)
              ·
                refine ⟨2111488439698051644377699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1407658959798701096251799 2111488439698051644377699)
                ·
                  refine ⟨3167232659547077466566549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2111488439698051644377699 3167232659547077466566549)
                  ·
                    refine ⟨148464030916269256245307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3167232659547077466566549 148464030916269256245307)
                    ·
                      rfl

theorem cell22_433699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 6].length) (baseStart_433699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_433699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_433699 prefixEnd_433699 := by exact prefixLift 433699
  have htrace : WordTrace (prefixWord ++ tailWord_433699) baseStart_433699 baseEnd_433699 := by
    simpa [prefixWord, tailWord_433699, baseEnd_433699] using wordTrace_append hprefix tailTrace_433699
  have hstable : (prefixWord ++ tailWord_433699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433699).length < 2 ^ (prefixWord ++ tailWord_433699).sum := by decide
  have hdescent : baseEnd_433699 < baseStart_433699 := by decide
  rcases family_descends (prefixWord ++ tailWord_433699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433718 : List Nat := [5, 1, 2, 1, 3, 1, 1, 1, 4, 3]
def baseStart_433718 : Nat := 118140960795 + 433718 * 2 ^ 59
def prefixEnd_433718 : Nat := 4983230072969 + 3 ^ 40 * 433718 * 2
def baseEnd_433718 : Nat := 148470535004559540020249

theorem tailTrace_433718 : CollatzResearch.WordTrace tailWord_433718 prefixEnd_433718 148470535004559540020249 := by
  unfold tailWord_433718
  simp only [CollatzResearch.WordTrace]
  refine ⟨988687190170077123890363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10545996695147489321497205 988687190170077123890363)
  ·
    refine ⟨1483030785255115685835545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 988687190170077123890363 1483030785255115685835545)
    ·
      refine ⟨1112273088941336764376659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1483030785255115685835545 1112273088941336764376659)
      ·
        refine ⟨1668409633412005146564989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1112273088941336764376659 1668409633412005146564989)
        ·
          refine ⟨625653612529501929961871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1668409633412005146564989 625653612529501929961871)
          ·
            refine ⟨938480418794252894942807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 625653612529501929961871 938480418794252894942807)
            ·
              refine ⟨1407720628191379342414211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 938480418794252894942807 1407720628191379342414211)
              ·
                refine ⟨2111580942287069013621317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1407720628191379342414211 2111580942287069013621317)
                ·
                  refine ⟨395921426678825440053997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2111580942287069013621317 395921426678825440053997)
                  ·
                    refine ⟨148470535004559540020249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 395921426678825440053997 148470535004559540020249)
                    ·
                      rfl

theorem cell22_433718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_433718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_433718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_433718 prefixEnd_433718 := by exact prefixLift 433718
  have htrace : WordTrace (prefixWord ++ tailWord_433718) baseStart_433718 baseEnd_433718 := by
    simpa [prefixWord, tailWord_433718, baseEnd_433718] using wordTrace_append hprefix tailTrace_433718
  have hstable : (prefixWord ++ tailWord_433718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433718).length < 2 ^ (prefixWord ++ tailWord_433718).sum := by decide
  have hdescent : baseEnd_433718 < baseStart_433718 := by decide
  rcases family_descends (prefixWord ++ tailWord_433718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433746 : List Nat := [3, 2, 2, 1, 2, 2, 2, 2, 3, 3]
def baseStart_433746 : Nat := 118140960795 + 433746 * 2 ^ 59
def prefixEnd_433746 : Nat := 4983230072969 + 3 ^ 40 * 433746 * 2
def baseEnd_433746 : Nat := 148480119976776800320163

theorem tailTrace_433746 : CollatzResearch.WordTrace tailWord_433746 prefixEnd_433746 148480119976776800320163 := by
  unfold tailWord_433746
  simp only [CollatzResearch.WordTrace]
  refine ⟨3955004071654948691066273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10546677524413196509510061 3955004071654948691066273)
  ·
    refine ⟨2966253053741211518299705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3955004071654948691066273 2966253053741211518299705)
    ·
      refine ⟨2224689790305908638724779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2966253053741211518299705 2224689790305908638724779)
      ·
        refine ⟨3337034685458862958087169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2224689790305908638724779 3337034685458862958087169)
        ·
          refine ⟨2502776014094147218565377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3337034685458862958087169 2502776014094147218565377)
          ·
            refine ⟨1877082010570610413924033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2502776014094147218565377 1877082010570610413924033)
            ·
              refine ⟨1407811507927957810443025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1877082010570610413924033 1407811507927957810443025)
              ·
                refine ⟨1055858630945968357832269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1407811507927957810443025 1055858630945968357832269)
                ·
                  refine ⟨395946986604738134187101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1055858630945968357832269 395946986604738134187101)
                  ·
                    refine ⟨148480119976776800320163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 395946986604738134187101 148480119976776800320163)
                    ·
                      rfl

theorem cell22_433746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_433746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_433746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_433746 prefixEnd_433746 := by exact prefixLift 433746
  have htrace : WordTrace (prefixWord ++ tailWord_433746) baseStart_433746 baseEnd_433746 := by
    simpa [prefixWord, tailWord_433746, baseEnd_433746] using wordTrace_append hprefix tailTrace_433746
  have hstable : (prefixWord ++ tailWord_433746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433746).length < 2 ^ (prefixWord ++ tailWord_433746).sum := by decide
  have hdescent : baseEnd_433746 < baseStart_433746 := by decide
  rcases family_descends (prefixWord ++ tailWord_433746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433763 : List Nat := [1, 1, 1, 5, 1, 3, 3, 3, 1, 3]
def baseStart_433763 : Nat := 118140960795 + 433763 * 2 ^ 59
def prefixEnd_433763 : Nat := 4983230072969 + 3 ^ 40 * 433763 * 2
def baseEnd_433763 : Nat := 148485939424194422645111

theorem tailTrace_433763 : CollatzResearch.WordTrace tailWord_433763 prefixEnd_433763 148485939424194422645111 := by
  unfold tailWord_433763
  simp only [CollatzResearch.WordTrace]
  refine ⟨15820636327558206667633943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10547090885038804445089295 15820636327558206667633943)
  ·
    refine ⟨23730954491337310001450915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15820636327558206667633943 23730954491337310001450915)
    ·
      refine ⟨35596431737005965002176373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23730954491337310001450915 35596431737005965002176373)
      ·
        refine ⟨3337165475344309218954035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35596431737005965002176373 3337165475344309218954035)
        ·
          refine ⟨5005748213016463828431053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3337165475344309218954035 5005748213016463828431053)
          ·
            refine ⟨1877155579881173935661645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5005748213016463828431053 1877155579881173935661645)
            ·
              refine ⟨703933342455440225873117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1877155579881173935661645 703933342455440225873117)
              ·
                refine ⟨263975003420790084702419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 703933342455440225873117 263975003420790084702419)
                ·
                  refine ⟨395962505131185127053629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 263975003420790084702419 395962505131185127053629)
                  ·
                    refine ⟨148485939424194422645111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 395962505131185127053629 148485939424194422645111)
                    ·
                      rfl

theorem cell22_433763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 3, 1, 3].length) (baseStart_433763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_433763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_433763 prefixEnd_433763 := by exact prefixLift 433763
  have htrace : WordTrace (prefixWord ++ tailWord_433763) baseStart_433763 baseEnd_433763 := by
    simpa [prefixWord, tailWord_433763, baseEnd_433763] using wordTrace_append hprefix tailTrace_433763
  have hstable : (prefixWord ++ tailWord_433763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433763).length < 2 ^ (prefixWord ++ tailWord_433763).sum := by decide
  have hdescent : baseEnd_433763 < baseStart_433763 := by decide
  rcases family_descends (prefixWord ++ tailWord_433763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433793 : List Nat := [1, 2, 4, 2, 1, 4, 2, 1, 5]
def baseStart_433793 : Nat := 118140960795 + 433793 * 2 ^ 59
def prefixEnd_433793 : Nat := 4983230072969 + 3 ^ 40 * 433793 * 2
def baseEnd_433793 : Nat := 49498736345761448131673

theorem tailTrace_433793 : CollatzResearch.WordTrace tailWord_433793 prefixEnd_433793 49498736345761448131673 := by
  unfold tailWord_433793
  simp only [CollatzResearch.WordTrace]
  refine ⟨15821730517449521791226033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10547820344966347860817355 15821730517449521791226033)
  ·
    refine ⟨11866297888087141343419525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15821730517449521791226033 11866297888087141343419525)
    ·
      refine ⟨2224930854016339001891161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11866297888087141343419525 2224930854016339001891161)
      ·
        refine ⟨1668698140512254251418371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2224930854016339001891161 1668698140512254251418371)
        ·
          refine ⟨2503047210768381377127557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1668698140512254251418371 2503047210768381377127557)
          ·
            refine ⟨469321352019071508211417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2503047210768381377127557 469321352019071508211417)
            ·
              refine ⟨351991014014303631158563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 469321352019071508211417 351991014014303631158563)
              ·
                refine ⟨527986521021455446737845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 351991014014303631158563 527986521021455446737845)
                ·
                  refine ⟨49498736345761448131673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 527986521021455446737845 49498736345761448131673)
                  ·
                    rfl

theorem cell22_433793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2, 1, 5].length) (baseStart_433793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_433793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_433793 prefixEnd_433793 := by exact prefixLift 433793
  have htrace : WordTrace (prefixWord ++ tailWord_433793) baseStart_433793 baseEnd_433793 := by
    simpa [prefixWord, tailWord_433793, baseEnd_433793] using wordTrace_append hprefix tailTrace_433793
  have hstable : (prefixWord ++ tailWord_433793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433793).length < 2 ^ (prefixWord ++ tailWord_433793).sum := by decide
  have hdescent : baseEnd_433793 < baseStart_433793 := by decide
  rcases family_descends (prefixWord ++ tailWord_433793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433806 : List Nat := [4, 1, 1, 3, 1, 3, 1, 1, 3, 4]
def baseStart_433806 : Nat := 118140960795 + 433806 * 2 ^ 59
def prefixEnd_433806 : Nat := 4983230072969 + 3 ^ 40 * 433806 * 2
def baseEnd_433806 : Nat := 148500659202956643819979

theorem tailTrace_433806 : CollatzResearch.WordTrace tailWord_433806 prefixEnd_433806 148500659202956643819979 := by
  unfold tailWord_433806
  simp only [CollatzResearch.WordTrace]
  refine ⟨1977775583300303126431159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10548136444268283340966181 1977775583300303126431159)
  ·
    refine ⟨2966663374950454689646739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1977775583300303126431159 2966663374950454689646739)
    ·
      refine ⟨4449995062425682034470109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2966663374950454689646739 4449995062425682034470109)
      ·
        refine ⟨1668748148409630762926291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4449995062425682034470109 1668748148409630762926291)
        ·
          refine ⟨2503122222614446144389437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1668748148409630762926291 2503122222614446144389437)
          ·
            refine ⟨938670833480417304146039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2503122222614446144389437 938670833480417304146039)
            ·
              refine ⟨1408006250220625956219059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 938670833480417304146039 1408006250220625956219059)
              ·
                refine ⟨2112009375330938934328589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1408006250220625956219059 2112009375330938934328589)
                ·
                  refine ⟨792003515749102100373221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2112009375330938934328589 792003515749102100373221)
                  ·
                    refine ⟨148500659202956643819979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 792003515749102100373221 148500659202956643819979)
                    ·
                      rfl

theorem cell22_433806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_433806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_433806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_433806 prefixEnd_433806 := by exact prefixLift 433806
  have htrace : WordTrace (prefixWord ++ tailWord_433806) baseStart_433806 baseEnd_433806 := by
    simpa [prefixWord, tailWord_433806, baseEnd_433806] using wordTrace_append hprefix tailTrace_433806
  have hstable : (prefixWord ++ tailWord_433806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433806).length < 2 ^ (prefixWord ++ tailWord_433806).sum := by decide
  have hdescent : baseEnd_433806 < baseStart_433806 := by decide
  rcases family_descends (prefixWord ++ tailWord_433806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433821 : List Nat := [1, 4, 2, 1, 1, 1, 1, 7, 4]
def baseStart_433821 : Nat := 118140960795 + 433821 * 2 ^ 59
def prefixEnd_433821 : Nat := 4983230072969 + 3 ^ 40 * 433821 * 2
def baseEnd_433821 : Nat := 49501931336500534898311

theorem tailTrace_433821 : CollatzResearch.WordTrace tailWord_433821 prefixEnd_433821 49501931336500534898311 := by
  unfold tailWord_433821
  simp only [CollatzResearch.WordTrace]
  refine ⟨15822751761348082573245317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10548501174232055048830211 15822751761348082573245317)
  ·
    refine ⟨2966765955252765482483497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15822751761348082573245317 2966765955252765482483497)
    ·
      refine ⟨2225074466439574111862623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2966765955252765482483497 2225074466439574111862623)
      ·
        refine ⟨3337611699659361167793935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2225074466439574111862623 3337611699659361167793935)
        ·
          refine ⟨5006417549489041751690903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3337611699659361167793935 5006417549489041751690903)
          ·
            refine ⟨7509626324233562627536355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5006417549489041751690903 7509626324233562627536355)
            ·
              refine ⟨11264439486350343941304533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7509626324233562627536355 11264439486350343941304533)
              ·
                refine ⟨264010300461336186124325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 11264439486350343941304533 264010300461336186124325)
                ·
                  refine ⟨49501931336500534898311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 264010300461336186124325 49501931336500534898311)
                  ·
                    rfl

theorem cell22_433821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 7, 4].length) (baseStart_433821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_433821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_433821 prefixEnd_433821 := by exact prefixLift 433821
  have htrace : WordTrace (prefixWord ++ tailWord_433821) baseStart_433821 baseEnd_433821 := by
    simpa [prefixWord, tailWord_433821, baseEnd_433821] using wordTrace_append hprefix tailTrace_433821
  have hstable : (prefixWord ++ tailWord_433821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433821).length < 2 ^ (prefixWord ++ tailWord_433821).sum := by decide
  have hdescent : baseEnd_433821 < baseStart_433821 := by decide
  rcases family_descends (prefixWord ++ tailWord_433821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433849 : List Nat := [1, 2, 1, 4, 1, 1, 5, 7]
def baseStart_433849 : Nat := 118140960795 + 433849 * 2 ^ 59
def prefixEnd_433849 : Nat := 4983230072969 + 3 ^ 40 * 433849 * 2
def baseEnd_433849 : Nat := 16501708775746540554983

theorem tailTrace_433849 : CollatzResearch.WordTrace tailWord_433849 prefixEnd_433849 16501708775746540554983 := by
  unfold tailWord_433849
  simp only [CollatzResearch.WordTrace]
  refine ⟨15823773005246643355264601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10549182003497762236843067 15823773005246643355264601)
  ·
    refine ⟨11867829753934982516448451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15823773005246643355264601 11867829753934982516448451)
    ·
      refine ⟨17801744630902473774672677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11867829753934982516448451 17801744630902473774672677)
      ·
        refine ⟨3337827118294213832751127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17801744630902473774672677 3337827118294213832751127)
        ·
          refine ⟨5006740677441320749126691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3337827118294213832751127 5006740677441320749126691)
          ·
            refine ⟨7510111016161981123690037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5006740677441320749126691 7510111016161981123690037)
            ·
              refine ⟨704072907765185730345941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7510111016161981123690037 704072907765185730345941)
              ·
                refine ⟨16501708775746540554983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 704072907765185730345941 16501708775746540554983)
                ·
                  rfl

theorem cell22_433849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 7].length) (baseStart_433849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_433849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_433849 prefixEnd_433849 := by exact prefixLift 433849
  have htrace : WordTrace (prefixWord ++ tailWord_433849) baseStart_433849 baseEnd_433849 := by
    simpa [prefixWord, tailWord_433849, baseEnd_433849] using wordTrace_append hprefix tailTrace_433849
  have hstable : (prefixWord ++ tailWord_433849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433849).length < 2 ^ (prefixWord ++ tailWord_433849).sum := by decide
  have hdescent : baseEnd_433849 < baseStart_433849 := by decide
  rcases family_descends (prefixWord ++ tailWord_433849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434005 : List Nat := [1, 3, 2, 2, 2, 3, 2, 2, 2, 3]
def baseStart_434005 : Nat := 118140960795 + 434005 * 2 ^ 59
def prefixEnd_434005 : Nat := 4983230072969 + 3 ^ 40 * 434005 * 2
def baseEnd_434005 : Nat := 148568780969786458094369

theorem tailTrace_434005 : CollatzResearch.WordTrace tailWord_434005 prefixEnd_434005 148568780969786458094369 := by
  unfold tailWord_434005
  simp only [CollatzResearch.WordTrace]
  refine ⟨15829462792681481997943469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10552975195120987998628979 15829462792681481997943469)
  ·
    refine ⟨5936048547255555749228801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15829462792681481997943469 5936048547255555749228801)
    ·
      refine ⟨4452036410441666811921601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5936048547255555749228801 4452036410441666811921601)
      ·
        refine ⟨3339027307831250108941201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4452036410441666811921601 3339027307831250108941201)
        ·
          refine ⟨2504270480873437581705901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3339027307831250108941201 2504270480873437581705901)
          ·
            refine ⟨939101430327539093139713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2504270480873437581705901 939101430327539093139713)
            ·
              refine ⟨704326072745654319854785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 939101430327539093139713 704326072745654319854785)
              ·
                refine ⟨528244554559240739891089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 704326072745654319854785 528244554559240739891089)
                ·
                  refine ⟨396183415919430554918317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 528244554559240739891089 396183415919430554918317)
                  ·
                    refine ⟨148568780969786458094369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 396183415919430554918317 148568780969786458094369)
                    ·
                      rfl

theorem cell22_434005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 2, 2, 3].length) (baseStart_434005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_434005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_434005 prefixEnd_434005 := by exact prefixLift 434005
  have htrace : WordTrace (prefixWord ++ tailWord_434005) baseStart_434005 baseEnd_434005 := by
    simpa [prefixWord, tailWord_434005, baseEnd_434005] using wordTrace_append hprefix tailTrace_434005
  have hstable : (prefixWord ++ tailWord_434005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434005).length < 2 ^ (prefixWord ++ tailWord_434005).sum := by decide
  have hdescent : baseEnd_434005 < baseStart_434005 := by decide
  rcases family_descends (prefixWord ++ tailWord_434005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434007 : List Nat := [1, 1, 3, 2, 5, 2, 2, 2, 4]
def baseStart_434007 : Nat := 118140960795 + 434007 * 2 ^ 59
def prefixEnd_434007 : Nat := 4983230072969 + 3 ^ 40 * 434007 * 2
def baseEnd_434007 : Nat := 49523155203553039848121

theorem tailTrace_434007 : CollatzResearch.WordTrace tailWord_434007 prefixEnd_434007 49523155203553039848121 := by
  unfold tailWord_434007
  simp only [CollatzResearch.WordTrace]
  refine ⟨15829535738674236339516275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10553023825782824226344183 15829535738674236339516275)
  ·
    refine ⟨23744303608011354509274413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15829535738674236339516275 23744303608011354509274413)
    ·
      refine ⟨8904113853004257940977905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23744303608011354509274413 8904113853004257940977905)
      ·
        refine ⟨6678085389753193455733429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8904113853004257940977905 6678085389753193455733429)
        ·
          refine ⟨626070505289361886475009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6678085389753193455733429 626070505289361886475009)
          ·
            refine ⟨469552878967021414856257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 626070505289361886475009 469552878967021414856257)
            ·
              refine ⟨352164659225266061142193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 469552878967021414856257 352164659225266061142193)
              ·
                refine ⟨264123494418949545856645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 352164659225266061142193 264123494418949545856645)
                ·
                  refine ⟨49523155203553039848121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 264123494418949545856645 49523155203553039848121)
                  ·
                    rfl

theorem cell22_434007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2, 2, 4].length) (baseStart_434007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_434007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_434007 prefixEnd_434007 := by exact prefixLift 434007
  have htrace : WordTrace (prefixWord ++ tailWord_434007) baseStart_434007 baseEnd_434007 := by
    simpa [prefixWord, tailWord_434007, baseEnd_434007] using wordTrace_append hprefix tailTrace_434007
  have hstable : (prefixWord ++ tailWord_434007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434007).length < 2 ^ (prefixWord ++ tailWord_434007).sum := by decide
  have hdescent : baseEnd_434007 < baseStart_434007 := by decide
  rcases family_descends (prefixWord ++ tailWord_434007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434018 : List Nat := [3, 3, 2, 1, 2, 1, 3, 7]
def baseStart_434018 : Nat := 118140960795 + 434018 * 2 ^ 59
def prefixEnd_434018 : Nat := 4983230072969 + 3 ^ 40 * 434018 * 2
def baseEnd_434018 : Nat := 16508136792828750835481

theorem tailTrace_434018 : CollatzResearch.WordTrace tailWord_434018 prefixEnd_434018 16508136792828750835481 := by
  unfold tailWord_434018
  simp only [CollatzResearch.WordTrace]
  refine ⟨3957484235408596304541677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10553291294422923478777805 3957484235408596304541677)
  ·
    refine ⟨1484056588278223614203129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3957484235408596304541677 1484056588278223614203129)
    ·
      refine ⟨1113042441208667710652347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1484056588278223614203129 1113042441208667710652347)
      ·
        refine ⟨1669563661813001565978521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1113042441208667710652347 1669563661813001565978521)
        ·
          refine ⟨1252172746359751174483891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1669563661813001565978521 1252172746359751174483891)
          ·
            refine ⟨1878259119539626761725837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1252172746359751174483891 1878259119539626761725837)
            ·
              refine ⟨704347169827360035647189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1878259119539626761725837 704347169827360035647189)
              ·
                refine ⟨16508136792828750835481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 704347169827360035647189 16508136792828750835481)
                ·
                  rfl

theorem cell22_434018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 7].length) (baseStart_434018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_434018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_434018 prefixEnd_434018 := by exact prefixLift 434018
  have htrace : WordTrace (prefixWord ++ tailWord_434018) baseStart_434018 baseEnd_434018 := by
    simpa [prefixWord, tailWord_434018, baseEnd_434018] using wordTrace_append hprefix tailTrace_434018
  have hstable : (prefixWord ++ tailWord_434018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434018).length < 2 ^ (prefixWord ++ tailWord_434018).sum := by decide
  have hdescent : baseEnd_434018 < baseStart_434018 := by decide
  rcases family_descends (prefixWord ++ tailWord_434018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434033 : List Nat := [1, 2, 2, 2, 1, 3, 3, 2, 3, 3]
def baseStart_434033 : Nat := 118140960795 + 434033 * 2 ^ 59
def prefixEnd_434033 : Nat := 4983230072969 + 3 ^ 40 * 434033 * 2
def baseEnd_434033 : Nat := 148578365942003718394283

theorem tailTrace_434033 : CollatzResearch.WordTrace tailWord_434033 prefixEnd_434033 148578365942003718394283 := by
  unfold tailWord_434033
  simp only [CollatzResearch.WordTrace]
  refine ⟨15830484036580042779962753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10553656024386695186641835 15830484036580042779962753)
  ·
    refine ⟨11872863027435032084972065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15830484036580042779962753 11872863027435032084972065)
    ·
      refine ⟨8904647270576274063729049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11872863027435032084972065 8904647270576274063729049)
      ·
        refine ⟨6678485452932205547796787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8904647270576274063729049 6678485452932205547796787)
        ·
          refine ⟨10017728179398308321695181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6678485452932205547796787 10017728179398308321695181)
          ·
            refine ⟨3756648067274365620635693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10017728179398308321695181 3756648067274365620635693)
            ·
              refine ⟨1408743025227887107738385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3756648067274365620635693 1408743025227887107738385)
              ·
                refine ⟨1056557268920915330803789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1408743025227887107738385 1056557268920915330803789)
                ·
                  refine ⟨396208975845343249051421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1056557268920915330803789 396208975845343249051421)
                  ·
                    refine ⟨148578365942003718394283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 396208975845343249051421 148578365942003718394283)
                    ·
                      rfl

theorem cell22_434033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2, 3, 3].length) (baseStart_434033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_434033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_434033 prefixEnd_434033 := by exact prefixLift 434033
  have htrace : WordTrace (prefixWord ++ tailWord_434033) baseStart_434033 baseEnd_434033 := by
    simpa [prefixWord, tailWord_434033, baseEnd_434033] using wordTrace_append hprefix tailTrace_434033
  have hstable : (prefixWord ++ tailWord_434033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434033).length < 2 ^ (prefixWord ++ tailWord_434033).sum := by decide
  have hdescent : baseEnd_434033 < baseStart_434033 := by decide
  rcases family_descends (prefixWord ++ tailWord_434033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434110 : List Nat := [4, 2, 1, 1, 1, 3, 2, 3, 1, 4]
def baseStart_434110 : Nat := 118140960795 + 434110 * 2 ^ 59
def prefixEnd_434110 : Nat := 4983230072969 + 3 ^ 40 * 434110 * 2
def baseEnd_434110 : Nat := 148604724615601184219047

theorem tailTrace_434110 : CollatzResearch.WordTrace tailWord_434110 prefixEnd_434110 148604724615601184219047 := by
  unfold tailWord_434110
  simp only [CollatzResearch.WordTrace]
  refine ⟨1979161557162635616314473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10555528304867389953677189 1979161557162635616314473)
  ·
    refine ⟨1484371167871976712235855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1979161557162635616314473 1484371167871976712235855)
    ·
      refine ⟨2226556751807965068353783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1484371167871976712235855 2226556751807965068353783)
      ·
        refine ⟨3339835127711947602530675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2226556751807965068353783 3339835127711947602530675)
        ·
          refine ⟨5009752691567921403796013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3339835127711947602530675 5009752691567921403796013)
          ·
            refine ⟨1878657259337970526423505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5009752691567921403796013 1878657259337970526423505)
            ·
              refine ⟨1408992944503477894817629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1878657259337970526423505 1408992944503477894817629)
              ·
                refine ⟨528372354188804210556611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1408992944503477894817629 528372354188804210556611)
                ·
                  refine ⟨792558531283206315834917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 528372354188804210556611 792558531283206315834917)
                  ·
                    refine ⟨148604724615601184219047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 792558531283206315834917 148604724615601184219047)
                    ·
                      rfl

theorem cell22_434110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_434110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_434110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_434110 prefixEnd_434110 := by exact prefixLift 434110
  have htrace : WordTrace (prefixWord ++ tailWord_434110) baseStart_434110 baseEnd_434110 := by
    simpa [prefixWord, tailWord_434110, baseEnd_434110] using wordTrace_append hprefix tailTrace_434110
  have hstable : (prefixWord ++ tailWord_434110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434110).length < 2 ^ (prefixWord ++ tailWord_434110).sum := by decide
  have hdescent : baseEnd_434110 < baseStart_434110 := by decide
  rcases family_descends (prefixWord ++ tailWord_434110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434123 : List Nat := [1, 1, 1, 1, 3, 4, 1, 3, 4, 3]
def baseStart_434123 : Nat := 118140960795 + 434123 * 2 ^ 59
def prefixEnd_434123 : Nat := 4983230072969 + 3 ^ 40 * 434123 * 2
def baseEnd_434123 : Nat := 148609174781273483644007

theorem tailTrace_434123 : CollatzResearch.WordTrace tailWord_434123 prefixEnd_434123 148609174781273483644007 := by
  unfold tailWord_434123
  simp only [CollatzResearch.WordTrace]
  refine ⟨15833766606253988150739023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10555844404169325433826015 15833766606253988150739023)
  ·
    refine ⟨23750649909380982226108535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15833766606253988150739023 23750649909380982226108535)
    ·
      refine ⟨35625974864071473339162803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23750649909380982226108535 35625974864071473339162803)
      ·
        refine ⟨53438962296107210008744205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35625974864071473339162803 53438962296107210008744205)
        ·
          refine ⟨20039610861040203753279077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53438962296107210008744205 20039610861040203753279077)
          ·
            refine ⟨3757427036445038203739827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20039610861040203753279077 3757427036445038203739827)
            ·
              refine ⟨5636140554667557305609741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3757427036445038203739827 5636140554667557305609741)
              ·
                refine ⟨2113552708000333989603653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5636140554667557305609741 2113552708000333989603653)
                ·
                  refine ⟨396291132750062623050685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2113552708000333989603653 396291132750062623050685)
                  ·
                    refine ⟨148609174781273483644007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 396291132750062623050685 148609174781273483644007)
                    ·
                      rfl

theorem cell22_434123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 4, 3].length) (baseStart_434123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_434123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_434123 prefixEnd_434123 := by exact prefixLift 434123
  have htrace : WordTrace (prefixWord ++ tailWord_434123) baseStart_434123 baseEnd_434123 := by
    simpa [prefixWord, tailWord_434123, baseEnd_434123] using wordTrace_append hprefix tailTrace_434123
  have hstable : (prefixWord ++ tailWord_434123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434123).length < 2 ^ (prefixWord ++ tailWord_434123).sum := by decide
  have hdescent : baseEnd_434123 < baseStart_434123 := by decide
  rcases family_descends (prefixWord ++ tailWord_434123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434157 : List Nat := [1, 5, 1, 4, 1, 1, 1, 2, 1, 5]
def baseStart_434157 : Nat := 118140960795 + 434157 * 2 ^ 59
def prefixEnd_434157 : Nat := 4983230072969 + 3 ^ 40 * 434157 * 2
def baseEnd_434157 : Nat := 148620813676108728293903

theorem tailTrace_434157 : CollatzResearch.WordTrace tailWord_434157 prefixEnd_434157 148620813676108728293903 := by
  unfold tailWord_434157
  simp only [CollatzResearch.WordTrace]
  refine ⟨15835006688130811957476725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10556671125420541304984483 15835006688130811957476725)
  ·
    refine ⟨1484531877012263621013443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15835006688130811957476725 1484531877012263621013443)
    ·
      refine ⟨2226797815518395431520165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1484531877012263621013443 2226797815518395431520165)
      ·
        refine ⟨417524590409699143410031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2226797815518395431520165 417524590409699143410031)
        ·
          refine ⟨626286885614548715115047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417524590409699143410031 626286885614548715115047)
          ·
            refine ⟨939430328421823072672571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 626286885614548715115047 939430328421823072672571)
            ·
              refine ⟨1409145492632734609008857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 939430328421823072672571 1409145492632734609008857)
              ·
                refine ⟨1056859119474550956756643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1409145492632734609008857 1056859119474550956756643)
                ·
                  refine ⟨1585288679211826435134965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1056859119474550956756643 1585288679211826435134965)
                  ·
                    refine ⟨148620813676108728293903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1585288679211826435134965 148620813676108728293903)
                    ·
                      rfl

theorem cell22_434157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_434157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_434157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_434157 prefixEnd_434157 := by exact prefixLift 434157
  have htrace : WordTrace (prefixWord ++ tailWord_434157) baseStart_434157 baseEnd_434157 := by
    simpa [prefixWord, tailWord_434157, baseEnd_434157] using wordTrace_append hprefix tailTrace_434157
  have hstable : (prefixWord ++ tailWord_434157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434157).length < 2 ^ (prefixWord ++ tailWord_434157).sum := by decide
  have hdescent : baseEnd_434157 < baseStart_434157 := by decide
  rcases family_descends (prefixWord ++ tailWord_434157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434174 : List Nat := [4, 2, 2, 2, 1, 2, 2, 2, 2, 3]
def baseStart_434174 : Nat := 118140960795 + 434174 * 2 ^ 59
def prefixEnd_434174 : Nat := 4983230072969 + 3 ^ 40 * 434174 * 2
def baseEnd_434174 : Nat := 148626633123526350618851

theorem tailTrace_434174 : CollatzResearch.WordTrace tailWord_434174 prefixEnd_434174 148626633123526350618851 := by
  unfold tailWord_434174
  simp only [CollatzResearch.WordTrace]
  refine ⟨1979453341133652982605697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10557084486046149240563717 1979453341133652982605697)
  ·
    refine ⟨1484590005850239736954273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1979453341133652982605697 1484590005850239736954273)
    ·
      refine ⟨1113442504387679802715705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1484590005850239736954273 1113442504387679802715705)
      ·
        refine ⟨835081878290759852036779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1113442504387679802715705 835081878290759852036779)
        ·
          refine ⟨1252622817436139778055169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 835081878290759852036779 1252622817436139778055169)
          ·
            refine ⟨939467113077104833541377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1252622817436139778055169 939467113077104833541377)
            ·
              refine ⟨704600334807828625156033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 939467113077104833541377 704600334807828625156033)
              ·
                refine ⟨528450251105871468867025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 704600334807828625156033 528450251105871468867025)
                ·
                  refine ⟨396337688329403601650269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 528450251105871468867025 396337688329403601650269)
                  ·
                    refine ⟨148626633123526350618851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 396337688329403601650269 148626633123526350618851)
                    ·
                      rfl

theorem cell22_434174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_434174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_434174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_434174 prefixEnd_434174 := by exact prefixLift 434174
  have htrace : WordTrace (prefixWord ++ tailWord_434174) baseStart_434174 baseEnd_434174 := by
    simpa [prefixWord, tailWord_434174, baseEnd_434174] using wordTrace_append hprefix tailTrace_434174
  have hstable : (prefixWord ++ tailWord_434174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434174).length < 2 ^ (prefixWord ++ tailWord_434174).sum := by decide
  have hdescent : baseEnd_434174 < baseStart_434174 := by decide
  rcases family_descends (prefixWord ++ tailWord_434174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434183 : List Nat := [1, 1, 4, 3, 1, 2, 1, 1, 2, 6]
def baseStart_434183 : Nat := 118140960795 + 434183 * 2 ^ 59
def prefixEnd_434183 : Nat := 4983230072969 + 3 ^ 40 * 434183 * 2
def baseEnd_434183 : Nat := 148629714007453327143823

theorem tailTrace_434183 : CollatzResearch.WordTrace tailWord_434183 prefixEnd_434183 148629714007453327143823 := by
  unfold tailWord_434183
  simp only [CollatzResearch.WordTrace]
  refine ⟨15835954986036618397923203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10557303324024412265282135 15835954986036618397923203)
  ·
    refine ⟨23753932479054927596884805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15835954986036618397923203 23753932479054927596884805)
    ·
      refine ⟨4453862339822798924415901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23753932479054927596884805 4453862339822798924415901)
      ·
        refine ⟨1670198377433549596655963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4453862339822798924415901 1670198377433549596655963)
        ·
          refine ⟨2505297566150324394983945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1670198377433549596655963 2505297566150324394983945)
          ·
            refine ⟨1878973174612743296237959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2505297566150324394983945 1878973174612743296237959)
            ·
              refine ⟨2818459761919114944356939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1878973174612743296237959 2818459761919114944356939)
              ·
                refine ⟨4227689642878672416535409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2818459761919114944356939 4227689642878672416535409)
                ·
                  refine ⟨3170767232159004312401557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4227689642878672416535409 3170767232159004312401557)
                  ·
                    refine ⟨148629714007453327143823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3170767232159004312401557 148629714007453327143823)
                    ·
                      rfl

theorem cell22_434183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_434183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_434183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_434183 prefixEnd_434183 := by exact prefixLift 434183
  have htrace : WordTrace (prefixWord ++ tailWord_434183) baseStart_434183 baseEnd_434183 := by
    simpa [prefixWord, tailWord_434183, baseEnd_434183] using wordTrace_append hprefix tailTrace_434183
  have hstable : (prefixWord ++ tailWord_434183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434183).length < 2 ^ (prefixWord ++ tailWord_434183).sum := by decide
  have hdescent : baseEnd_434183 < baseStart_434183 := by decide
  rcases family_descends (prefixWord ++ tailWord_434183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434230 : List Nat := [5, 1, 2, 1, 1, 1, 1, 1, 4, 5]
def baseStart_434230 : Nat := 118140960795 + 434230 * 2 ^ 59
def prefixEnd_434230 : Nat := 4983230072969 + 3 ^ 40 * 434230 * 2
def baseEnd_434230 : Nat := 148645803067960871218679

theorem tailTrace_434230 : CollatzResearch.WordTrace tailWord_434230 prefixEnd_434230 148645803067960871218679 := by
  unfold tailWord_434230
  simp only [CollatzResearch.WordTrace]
  refine ⟨989854326054146589055259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10558446144577563616589429 989854326054146589055259)
  ·
    refine ⟨1484781489081219883582889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 989854326054146589055259 1484781489081219883582889)
    ·
      refine ⟨1113586116810914912687167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1484781489081219883582889 1113586116810914912687167)
      ·
        refine ⟨1670379175216372369030751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1113586116810914912687167 1670379175216372369030751)
        ·
          refine ⟨2505568762824558553546127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1670379175216372369030751 2505568762824558553546127)
          ·
            refine ⟨3758353144236837830319191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2505568762824558553546127 3758353144236837830319191)
            ·
              refine ⟨5637529716355256745478787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3758353144236837830319191 5637529716355256745478787)
              ·
                refine ⟨8456294574532885118218181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5637529716355256745478787 8456294574532885118218181)
                ·
                  refine ⟨1585555232724915959665909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8456294574532885118218181 1585555232724915959665909)
                  ·
                    refine ⟨148645803067960871218679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1585555232724915959665909 148645803067960871218679)
                    ·
                      rfl

theorem cell22_434230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_434230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_434230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_434230 prefixEnd_434230 := by exact prefixLift 434230
  have htrace : WordTrace (prefixWord ++ tailWord_434230) baseStart_434230 baseEnd_434230 := by
    simpa [prefixWord, tailWord_434230, baseEnd_434230] using wordTrace_append hprefix tailTrace_434230
  have hstable : (prefixWord ++ tailWord_434230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434230).length < 2 ^ (prefixWord ++ tailWord_434230).sum := by decide
  have hdescent : baseEnd_434230 < baseStart_434230 := by decide
  rcases family_descends (prefixWord ++ tailWord_434230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434232 : List Nat := [2, 1, 2, 1, 6, 2, 1, 2, 5]
def baseStart_434232 : Nat := 118140960795 + 434232 * 2 ^ 59
def prefixEnd_434232 : Nat := 4983230072969 + 3 ^ 40 * 434232 * 2
def baseEnd_434232 : Nat := 49548829236277844222891

theorem tailTrace_434232 : CollatzResearch.WordTrace tailWord_434232 prefixEnd_434232 49548829236277844222891 := by
  unfold tailWord_434232
  simp only [CollatzResearch.WordTrace]
  refine ⟨7918871081429549883228475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10558494775239399844304633 7918871081429549883228475)
  ·
    refine ⟨11878306622144324824842713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7918871081429549883228475 11878306622144324824842713)
    ·
      refine ⟨8908729966608243618632035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11878306622144324824842713 8908729966608243618632035)
      ·
        refine ⟨13363094949912365427948053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8908729966608243618632035 13363094949912365427948053)
        ·
          refine ⟨626395075777142129435065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13363094949912365427948053 626395075777142129435065)
          ·
            refine ⟨469796306832856597076299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 626395075777142129435065 469796306832856597076299)
            ·
              refine ⟨704694460249284895614449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 469796306832856597076299 704694460249284895614449)
              ·
                refine ⟨528520845186963671710837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 704694460249284895614449 528520845186963671710837)
                ·
                  refine ⟨49548829236277844222891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 528520845186963671710837 49548829236277844222891)
                  ·
                    rfl

theorem cell22_434232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 2, 5].length) (baseStart_434232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_434232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_434232 prefixEnd_434232 := by exact prefixLift 434232
  have htrace : WordTrace (prefixWord ++ tailWord_434232) baseStart_434232 baseEnd_434232 := by
    simpa [prefixWord, tailWord_434232, baseEnd_434232] using wordTrace_append hprefix tailTrace_434232
  have hstable : (prefixWord ++ tailWord_434232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434232).length < 2 ^ (prefixWord ++ tailWord_434232).sum := by decide
  have hdescent : baseEnd_434232 < baseStart_434232 := by decide
  rcases family_descends (prefixWord ++ tailWord_434232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434270 : List Nat := [4, 4, 1, 1, 2, 2, 1, 3, 1, 3]
def baseStart_434270 : Nat := 118140960795 + 434270 * 2 ^ 59
def prefixEnd_434270 : Nat := 4983230072969 + 3 ^ 40 * 434270 * 2
def baseEnd_434270 : Nat := 148659495885414100218557

theorem tailTrace_434270 : CollatzResearch.WordTrace tailWord_434270 prefixEnd_434270 148659495885414100218557 := by
  unfold tailWord_434270
  simp only [CollatzResearch.WordTrace]
  refine ⟨1979891017090179032042533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10559418757814288170893509 1979891017090179032042533)
  ·
    refine ⟨371229565704408568507975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1979891017090179032042533 371229565704408568507975)
    ·
      refine ⟨556844348556612852761963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371229565704408568507975 556844348556612852761963)
      ·
        refine ⟨835266522834919279142945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 556844348556612852761963 835266522834919279142945)
        ·
          refine ⟨626449892126189459357209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 835266522834919279142945 626449892126189459357209)
          ·
            refine ⟨469837419094642094517907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 626449892126189459357209 469837419094642094517907)
            ·
              refine ⟨704756128641963141776861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 469837419094642094517907 704756128641963141776861)
              ·
                refine ⟨264283548240736178166323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 704756128641963141776861 264283548240736178166323)
                ·
                  refine ⟨396425322361104267249485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 264283548240736178166323 396425322361104267249485)
                  ·
                    refine ⟨148659495885414100218557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 396425322361104267249485 148659495885414100218557)
                    ·
                      rfl

theorem cell22_434270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_434270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_434270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_434270 prefixEnd_434270 := by exact prefixLift 434270
  have htrace : WordTrace (prefixWord ++ tailWord_434270) baseStart_434270 baseEnd_434270 := by
    simpa [prefixWord, tailWord_434270, baseEnd_434270] using wordTrace_append hprefix tailTrace_434270
  have hstable : (prefixWord ++ tailWord_434270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434270).length < 2 ^ (prefixWord ++ tailWord_434270).sum := by decide
  have hdescent : baseEnd_434270 < baseStart_434270 := by decide
  rcases family_descends (prefixWord ++ tailWord_434270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434275 : List Nat := [1, 1, 1, 5, 1, 1, 3, 2, 4, 3]
def baseStart_434275 : Nat := 118140960795 + 434275 * 2 ^ 59
def prefixEnd_434275 : Nat := 4983230072969 + 3 ^ 40 * 434275 * 2
def baseEnd_434275 : Nat := 148661207487595753843541

theorem tailTrace_434275 : CollatzResearch.WordTrace tailWord_434275 prefixEnd_434275 148661207487595753843541 := by
  unfold tailWord_434275
  simp only [CollatzResearch.WordTrace]
  refine ⟨15839310501703318110272279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10559540334468878740181519 15839310501703318110272279)
  ·
    refine ⟨23758965752554977165408419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15839310501703318110272279 23758965752554977165408419)
    ·
      refine ⟨35638448628832465748112629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23758965752554977165408419 35638448628832465748112629)
      ·
        refine ⟨3341104558953043663885559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35638448628832465748112629 3341104558953043663885559)
        ·
          refine ⟨5011656838429565495828339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3341104558953043663885559 5011656838429565495828339)
          ·
            refine ⟨7517485257644348243742509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5011656838429565495828339 7517485257644348243742509)
            ·
              refine ⟨2819056971616630591403441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7517485257644348243742509 2819056971616630591403441)
              ·
                refine ⟨2114292728712472943552581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2819056971616630591403441 2114292728712472943552581)
                ·
                  refine ⟨396429886633588676916109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2114292728712472943552581 396429886633588676916109)
                  ·
                    refine ⟨148661207487595753843541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 396429886633588676916109 148661207487595753843541)
                    ·
                      rfl

theorem cell22_434275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 4, 3].length) (baseStart_434275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_434275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_434275 prefixEnd_434275 := by exact prefixLift 434275
  have htrace : WordTrace (prefixWord ++ tailWord_434275) baseStart_434275 baseEnd_434275 := by
    simpa [prefixWord, tailWord_434275, baseEnd_434275] using wordTrace_append hprefix tailTrace_434275
  have hstable : (prefixWord ++ tailWord_434275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434275).length < 2 ^ (prefixWord ++ tailWord_434275).sum := by decide
  have hdescent : baseEnd_434275 < baseStart_434275 := by decide
  rcases family_descends (prefixWord ++ tailWord_434275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434277 : List Nat := [1, 3, 1, 3, 2, 2, 3, 3, 4]
def baseStart_434277 : Nat := 118140960795 + 434277 * 2 ^ 59
def prefixEnd_434277 : Nat := 4983230072969 + 3 ^ 40 * 434277 * 2
def baseEnd_434277 : Nat := 49553964042822805097845

theorem tailTrace_434277 : CollatzResearch.WordTrace tailWord_434277 prefixEnd_434277 49553964042822805097845 := by
  unfold tailWord_434277
  simp only [CollatzResearch.WordTrace]
  refine ⟨15839383447696072451845085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10559588965130714967896723 15839383447696072451845085)
  ·
    refine ⟨5939768792886027169441907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15839383447696072451845085 5939768792886027169441907)
    ·
      refine ⟨8909653189329040754162861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5939768792886027169441907 8909653189329040754162861)
      ·
        refine ⟨3341119945998390282811073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8909653189329040754162861 3341119945998390282811073)
        ·
          refine ⟨2505839959498792712108305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3341119945998390282811073 2505839959498792712108305)
          ·
            refine ⟨1879379969624094534081229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2505839959498792712108305 1879379969624094534081229)
            ·
              refine ⟨704767488609035450280461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1879379969624094534081229 704767488609035450280461)
              ·
                refine ⟨264287808228388293855173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 704767488609035450280461 264287808228388293855173)
                ·
                  refine ⟨49553964042822805097845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 264287808228388293855173 49553964042822805097845)
                  ·
                    rfl

theorem cell22_434277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 3, 4].length) (baseStart_434277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_434277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_434277 prefixEnd_434277 := by exact prefixLift 434277
  have htrace : WordTrace (prefixWord ++ tailWord_434277) baseStart_434277 baseEnd_434277 := by
    simpa [prefixWord, tailWord_434277, baseEnd_434277] using wordTrace_append hprefix tailTrace_434277
  have hstable : (prefixWord ++ tailWord_434277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434277).length < 2 ^ (prefixWord ++ tailWord_434277).sum := by decide
  have hdescent : baseEnd_434277 < baseStart_434277 := by decide
  rcases family_descends (prefixWord ++ tailWord_434277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434288 : List Nat := [2, 1, 1, 1, 5, 2, 10]
def baseStart_434288 : Nat := 118140960795 + 434288 * 2 ^ 59
def prefixEnd_434288 : Nat := 4983230072969 + 3 ^ 40 * 434288 * 2
def baseEnd_434288 : Nat := 5506135468639557528463

theorem tailTrace_434288 : CollatzResearch.WordTrace tailWord_434288 prefixEnd_434288 5506135468639557528463 := by
  unfold tailWord_434288
  simp only [CollatzResearch.WordTrace]
  refine ⟨7919892325328110665247759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10559856433770814220330345 7919892325328110665247759)
  ·
    refine ⟨11879838487992165997871639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7919892325328110665247759 11879838487992165997871639)
    ·
      refine ⟨17819757731988248996807459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11879838487992165997871639 17819757731988248996807459)
      ·
        refine ⟨26729636597982373495211189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17819757731988248996807459 26729636597982373495211189)
        ·
          refine ⟨2505903431060847515176049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26729636597982373495211189 2505903431060847515176049)
          ·
            refine ⟨1879427573295635636382037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2505903431060847515176049 1879427573295635636382037)
            ·
              refine ⟨5506135468639557528463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1879427573295635636382037 5506135468639557528463)
              ·
                rfl

theorem cell22_434288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 10].length) (baseStart_434288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_434288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_434288 prefixEnd_434288 := by exact prefixLift 434288
  have htrace : WordTrace (prefixWord ++ tailWord_434288) baseStart_434288 baseEnd_434288 := by
    simpa [prefixWord, tailWord_434288, baseEnd_434288] using wordTrace_append hprefix tailTrace_434288
  have hstable : (prefixWord ++ tailWord_434288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434288).length < 2 ^ (prefixWord ++ tailWord_434288).sum := by decide
  have hdescent : baseEnd_434288 < baseStart_434288 := by decide
  rcases family_descends (prefixWord ++ tailWord_434288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434290 : List Nat := [3, 2, 1, 2, 2, 2, 1, 1, 4, 4]
def baseStart_434290 : Nat := 118140960795 + 434290 * 2 ^ 59
def prefixEnd_434290 : Nat := 4983230072969 + 3 ^ 40 * 434290 * 2
def baseEnd_434290 : Nat := 148666342294140714718495

theorem tailTrace_434290 : CollatzResearch.WordTrace tailWord_434290 prefixEnd_434290 148666342294140714718495 := by
  unfold tailWord_434290
  simp only [CollatzResearch.WordTrace]
  refine ⟨3959964399162243918017081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10559905064432650448045549 3959964399162243918017081)
  ·
    refine ⟨2969973299371682938512811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3959964399162243918017081 2969973299371682938512811)
    ·
      refine ⟨4454959949057524407769217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2969973299371682938512811 4454959949057524407769217)
      ·
        refine ⟨3341219961793143305826913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4454959949057524407769217 3341219961793143305826913)
        ·
          refine ⟨2505914971344857479370185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3341219961793143305826913 2505914971344857479370185)
          ·
            refine ⟨1879436228508643109527639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2505914971344857479370185 1879436228508643109527639)
            ·
              refine ⟨2819154342762964664291459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1879436228508643109527639 2819154342762964664291459)
              ·
                refine ⟨4228731514144446996437189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2819154342762964664291459 4228731514144446996437189)
                ·
                  refine ⟨792887158902083811831973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4228731514144446996437189 792887158902083811831973)
                  ·
                    refine ⟨148666342294140714718495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 792887158902083811831973 148666342294140714718495)
                    ·
                      rfl

theorem cell22_434290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_434290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_434290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_434290 prefixEnd_434290 := by exact prefixLift 434290
  have htrace : WordTrace (prefixWord ++ tailWord_434290) baseStart_434290 baseEnd_434290 := by
    simpa [prefixWord, tailWord_434290, baseEnd_434290] using wordTrace_append hprefix tailTrace_434290
  have hstable : (prefixWord ++ tailWord_434290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434290).length < 2 ^ (prefixWord ++ tailWord_434290).sum := by decide
  have hdescent : baseEnd_434290 < baseStart_434290 := by decide
  rcases family_descends (prefixWord ++ tailWord_434290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434309 : List Nat := [1, 3, 1, 1, 5, 1, 4, 1, 2, 3]
def baseStart_434309 : Nat := 118140960795 + 434309 * 2 ^ 59
def prefixEnd_434309 : Nat := 4983230072969 + 3 ^ 40 * 434309 * 2
def baseEnd_434309 : Nat := 148672846382430998493437

theorem tailTrace_434309 : CollatzResearch.WordTrace tailWord_434309 prefixEnd_434309 148672846382430998493437 := by
  unfold tailWord_434309
  simp only [CollatzResearch.WordTrace]
  refine ⟨15840550583580141917009981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10560367055720094611339987 15840550583580141917009981)
  ·
    refine ⟨5940206468842553218878743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15840550583580141917009981 5940206468842553218878743)
    ·
      refine ⟨8910309703263829828318115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5940206468842553218878743 8910309703263829828318115)
      ·
        refine ⟨13365464554895744742477173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8910309703263829828318115 13365464554895744742477173)
        ·
          refine ⟨1253012302021476069607235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13365464554895744742477173 1253012302021476069607235)
          ·
            refine ⟨1879518453032214104410853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1253012302021476069607235 1879518453032214104410853)
            ·
              refine ⟨352409709943540144577035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1879518453032214104410853 352409709943540144577035)
              ·
                refine ⟨528614564915310216865553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 352409709943540144577035 528614564915310216865553)
                ·
                  refine ⟨396460923686482662649165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 528614564915310216865553 396460923686482662649165)
                  ·
                    refine ⟨148672846382430998493437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 396460923686482662649165 148672846382430998493437)
                    ·
                      rfl

theorem cell22_434309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4, 1, 2, 3].length) (baseStart_434309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_434309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_434309 prefixEnd_434309 := by exact prefixLift 434309
  have htrace : WordTrace (prefixWord ++ tailWord_434309) baseStart_434309 baseEnd_434309 := by
    simpa [prefixWord, tailWord_434309, baseEnd_434309] using wordTrace_append hprefix tailTrace_434309
  have hstable : (prefixWord ++ tailWord_434309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434309).length < 2 ^ (prefixWord ++ tailWord_434309).sum := by decide
  have hdescent : baseEnd_434309 < baseStart_434309 := by decide
  rcases family_descends (prefixWord ++ tailWord_434309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434320 : List Nat := [2, 1, 1, 1, 1, 1, 6, 1, 5, 3]
def baseStart_434320 : Nat := 118140960795 + 434320 * 2 ^ 59
def prefixEnd_434320 : Nat := 4983230072969 + 3 ^ 40 * 434320 * 2
def baseEnd_434320 : Nat := 148676611907230636468403

theorem tailTrace_434320 : CollatzResearch.WordTrace tailWord_434320 prefixEnd_434320 148676611907230636468403 := by
  unfold tailWord_434320
  simp only [CollatzResearch.WordTrace]
  refine ⟨7920475893270145397830207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10560634524360193863773609 7920475893270145397830207)
  ·
    refine ⟨11880713839905218096745311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7920475893270145397830207 11880713839905218096745311)
    ·
      refine ⟨17821070759857827145117967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11880713839905218096745311 17821070759857827145117967)
      ·
        refine ⟨26731606139786740717676951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17821070759857827145117967 26731606139786740717676951)
        ·
          refine ⟨40097409209680111076515427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26731606139786740717676951 40097409209680111076515427)
          ·
            refine ⟨60146113814520166614773141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40097409209680111076515427 60146113814520166614773141)
            ·
              refine ⟨2819349085055632810067491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 60146113814520166614773141 2819349085055632810067491)
              ·
                refine ⟨4229023627583449215101237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2819349085055632810067491 4229023627583449215101237)
                ·
                  refine ⟨396470965085948363915741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4229023627583449215101237 396470965085948363915741)
                  ·
                    refine ⟨148676611907230636468403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 396470965085948363915741 148676611907230636468403)
                    ·
                      rfl

theorem cell22_434320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 5, 3].length) (baseStart_434320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_434320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_434320 prefixEnd_434320 := by exact prefixLift 434320
  have htrace : WordTrace (prefixWord ++ tailWord_434320) baseStart_434320 baseEnd_434320 := by
    simpa [prefixWord, tailWord_434320, baseEnd_434320] using wordTrace_append hprefix tailTrace_434320
  have hstable : (prefixWord ++ tailWord_434320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434320).length < 2 ^ (prefixWord ++ tailWord_434320).sum := by decide
  have hdescent : baseEnd_434320 < baseStart_434320 := by decide
  rcases family_descends (prefixWord ++ tailWord_434320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434354 : List Nat := [3, 2, 1, 1, 1, 3, 3, 4, 1, 3]
def baseStart_434354 : Nat := 118140960795 + 434354 * 2 ^ 59
def prefixEnd_434354 : Nat := 4983230072969 + 3 ^ 40 * 434354 * 2
def baseEnd_434354 : Nat := 148688250802065881118299

theorem tailTrace_434354 : CollatzResearch.WordTrace tailWord_434354 prefixEnd_434354 148688250802065881118299 := by
  unfold tailWord_434354
  simp only [CollatzResearch.WordTrace]
  refine ⟨3960547967104278650599529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10561461245611409734932077 3960547967104278650599529)
  ·
    refine ⟨2970410975328208987949647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3960547967104278650599529 2970410975328208987949647)
    ·
      refine ⟨4455616462992313481924471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2970410975328208987949647 4455616462992313481924471)
      ·
        refine ⟨6683424694488470222886707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4455616462992313481924471 6683424694488470222886707)
        ·
          refine ⟨10025137041732705334330061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6683424694488470222886707 10025137041732705334330061)
          ·
            refine ⟨3759426390649764500373773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10025137041732705334330061 3759426390649764500373773)
            ·
              refine ⟨1409784896493661687640165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3759426390649764500373773 1409784896493661687640165)
              ·
                refine ⟨264334668092561566432531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1409784896493661687640165 264334668092561566432531)
                ·
                  refine ⟨396502002138842349648797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 264334668092561566432531 396502002138842349648797)
                  ·
                    refine ⟨148688250802065881118299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 396502002138842349648797 148688250802065881118299)
                    ·
                      rfl

theorem cell22_434354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 4, 1, 3].length) (baseStart_434354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_434354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_434354 prefixEnd_434354 := by exact prefixLift 434354
  have htrace : WordTrace (prefixWord ++ tailWord_434354) baseStart_434354 baseEnd_434354 := by
    simpa [prefixWord, tailWord_434354, baseEnd_434354] using wordTrace_append hprefix tailTrace_434354
  have hstable : (prefixWord ++ tailWord_434354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434354).length < 2 ^ (prefixWord ++ tailWord_434354).sum := by decide
  have hdescent : baseEnd_434354 < baseStart_434354 := by decide
  rcases family_descends (prefixWord ++ tailWord_434354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434412 : List Nat := [2, 2, 1, 1, 2, 3, 1, 6, 4]
def baseStart_434412 : Nat := 118140960795 + 434412 * 2 ^ 59
def prefixEnd_434412 : Nat := 4983230072969 + 3 ^ 40 * 434412 * 2
def baseEnd_434412 : Nat := 49569368462457687722707

theorem tailTrace_434412 : CollatzResearch.WordTrace tailWord_434412 prefixEnd_434412 49569368462457687722707 := by
  unfold tailWord_434412
  simp only [CollatzResearch.WordTrace]
  refine ⟨7922153651103495254004745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10562871534804660338672993 7922153651103495254004745)
  ·
    refine ⟨5941615238327621440503559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7922153651103495254004745 5941615238327621440503559)
    ·
      refine ⟨8912422857491432160755339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5941615238327621440503559 8912422857491432160755339)
      ·
        refine ⟨13368634286237148241133009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8912422857491432160755339 13368634286237148241133009)
        ·
          refine ⟨10026475714677861180849757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13368634286237148241133009 10026475714677861180849757)
          ·
            refine ⟨3759928393004197942818659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10026475714677861180849757 3759928393004197942818659)
            ·
              refine ⟨5639892589506296914227989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3759928393004197942818659 5639892589506296914227989)
              ·
                refine ⟨264369965133107667854437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5639892589506296914227989 264369965133107667854437)
                ·
                  refine ⟨49569368462457687722707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 264369965133107667854437 49569368462457687722707)
                  ·
                    rfl

theorem cell22_434412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 6, 4].length) (baseStart_434412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_434412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_434412 prefixEnd_434412 := by exact prefixLift 434412
  have htrace : WordTrace (prefixWord ++ tailWord_434412) baseStart_434412 baseEnd_434412 := by
    simpa [prefixWord, tailWord_434412, baseEnd_434412] using wordTrace_append hprefix tailTrace_434412
  have hstable : (prefixWord ++ tailWord_434412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434412).length < 2 ^ (prefixWord ++ tailWord_434412).sum := by decide
  have hdescent : baseEnd_434412 < baseStart_434412 := by decide
  rcases family_descends (prefixWord ++ tailWord_434412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434425 : List Nat := [1, 2, 1, 3, 1, 1, 2, 1, 6, 4]
def baseStart_434425 : Nat := 118140960795 + 434425 * 2 ^ 59
def prefixEnd_434425 : Nat := 4983230072969 + 3 ^ 40 * 434425 * 2
def baseEnd_434425 : Nat := 148712555553045362593081

theorem tailTrace_434425 : CollatzResearch.WordTrace tailWord_434425 prefixEnd_434425 148712555553045362593081 := by
  unfold tailWord_434425
  simp only [CollatzResearch.WordTrace]
  refine ⟨15844781451159893728232729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10563187634106595818821819 15844781451159893728232729)
  ·
    refine ⟨11883586088369920296174547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15844781451159893728232729 11883586088369920296174547)
    ·
      refine ⟨17825379132554880444261821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11883586088369920296174547 17825379132554880444261821)
      ·
        refine ⟨6684517174708080166598183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17825379132554880444261821 6684517174708080166598183)
        ·
          refine ⟨10026775762062120249897275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6684517174708080166598183 10026775762062120249897275)
          ·
            refine ⟨15040163643093180374845913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10026775762062120249897275 15040163643093180374845913)
            ·
              refine ⟨11280122732319885281134435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15040163643093180374845913 11280122732319885281134435)
              ·
                refine ⟨16920184098479827921701653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11280122732319885281134435 16920184098479827921701653)
                ·
                  refine ⟨793133629616241933829765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 16920184098479827921701653 793133629616241933829765)
                  ·
                    refine ⟨148712555553045362593081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 793133629616241933829765 148712555553045362593081)
                    ·
                      rfl

theorem cell22_434425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 6, 4].length) (baseStart_434425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_434425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_434425 prefixEnd_434425 := by exact prefixLift 434425
  have htrace : WordTrace (prefixWord ++ tailWord_434425) baseStart_434425 baseEnd_434425 := by
    simpa [prefixWord, tailWord_434425, baseEnd_434425] using wordTrace_append hprefix tailTrace_434425
  have hstable : (prefixWord ++ tailWord_434425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434425).length < 2 ^ (prefixWord ++ tailWord_434425).sum := by decide
  have hdescent : baseEnd_434425 < baseStart_434425 := by decide
  rcases family_descends (prefixWord ++ tailWord_434425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434474 : List Nat := [3, 1, 4, 2, 2, 1, 2, 7]
def baseStart_434474 : Nat := 118140960795 + 434474 * 2 ^ 59
def prefixEnd_434474 : Nat := 4983230072969 + 3 ^ 40 * 434474 * 2
def baseEnd_434474 : Nat := 16525481028269507568659

theorem tailTrace_434474 : CollatzResearch.WordTrace tailWord_434474 prefixEnd_434474 16525481028269507568659 := by
  unfold tailWord_434474
  simp only [CollatzResearch.WordTrace]
  refine ⟨3961642156995593774191619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10564379085321583397844317 3961642156995593774191619)
  ·
    refine ⟨5942463235493390661287429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3961642156995593774191619 5942463235493390661287429)
    ·
      refine ⟨1114211856655010748991393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5942463235493390661287429 1114211856655010748991393)
      ·
        refine ⟨835658892491258061743545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1114211856655010748991393 835658892491258061743545)
        ·
          refine ⟨626744169368443546307659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 835658892491258061743545 626744169368443546307659)
          ·
            refine ⟨940116254052665319461489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 626744169368443546307659 940116254052665319461489)
            ·
              refine ⟨705087190539498989596117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 940116254052665319461489 705087190539498989596117)
              ·
                refine ⟨16525481028269507568659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 705087190539498989596117 16525481028269507568659)
                ·
                  rfl

theorem cell22_434474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 7].length) (baseStart_434474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_434474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_434474 prefixEnd_434474 := by exact prefixLift 434474
  have htrace : WordTrace (prefixWord ++ tailWord_434474) baseStart_434474 baseEnd_434474 := by
    simpa [prefixWord, tailWord_434474, baseEnd_434474] using wordTrace_append hprefix tailTrace_434474
  have hstable : (prefixWord ++ tailWord_434474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434474).length < 2 ^ (prefixWord ++ tailWord_434474).sum := by decide
  have hdescent : baseEnd_434474 < baseStart_434474 := by decide
  rcases family_descends (prefixWord ++ tailWord_434474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434478 : List Nat := [4, 1, 3, 3, 1, 1, 1, 3, 2, 3]
def baseStart_434478 : Nat := 118140960795 + 434478 * 2 ^ 59
def prefixEnd_434478 : Nat := 4983230072969 + 3 ^ 40 * 434478 * 2
def baseEnd_434478 : Nat := 148730698536170891017919

theorem tailTrace_434478 : CollatzResearch.WordTrace tailWord_434478 prefixEnd_434478 148730698536170891017919 := by
  unfold tailWord_434478
  simp only [CollatzResearch.WordTrace]
  refine ⟨1980839314995985472489011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10564476346645255853274725 1980839314995985472489011)
  ·
    refine ⟨2971258972493978208733517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1980839314995985472489011 2971258972493978208733517)
    ·
      refine ⟨1114222114685241828275069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2971258972493978208733517 1114222114685241828275069)
      ·
        refine ⟨417833293006965685603151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1114222114685241828275069 417833293006965685603151)
        ·
          refine ⟨626749939510448528404727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417833293006965685603151 626749939510448528404727)
          ·
            refine ⟨940124909265672792607091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 626749939510448528404727 940124909265672792607091)
            ·
              refine ⟨1410187363898509188910637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 940124909265672792607091 1410187363898509188910637)
              ·
                refine ⟨528820261461940945841489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1410187363898509188910637 528820261461940945841489)
                ·
                  refine ⟨396615196096455709381117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 528820261461940945841489 396615196096455709381117)
                  ·
                    refine ⟨148730698536170891017919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 396615196096455709381117 148730698536170891017919)
                    ·
                      rfl

theorem cell22_434478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_434478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_434478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_434478 prefixEnd_434478 := by exact prefixLift 434478
  have htrace : WordTrace (prefixWord ++ tailWord_434478) baseStart_434478 baseEnd_434478 := by
    simpa [prefixWord, tailWord_434478, baseEnd_434478] using wordTrace_append hprefix tailTrace_434478
  have hstable : (prefixWord ++ tailWord_434478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434478).length < 2 ^ (prefixWord ++ tailWord_434478).sum := by decide
  have hdescent : baseEnd_434478 < baseStart_434478 := by decide
  rcases family_descends (prefixWord ++ tailWord_434478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434532 : List Nat := [2, 3, 1, 1, 3, 1, 1, 1, 5, 4]
def baseStart_434532 : Nat := 118140960795 + 434532 * 2 ^ 59
def prefixEnd_434532 : Nat := 4983230072969 + 3 ^ 40 * 434532 * 2
def baseEnd_434532 : Nat := 148749183839732750167753

theorem tailTrace_434532 : CollatzResearch.WordTrace tailWord_434532 prefixEnd_434532 148749183839732750167753 := by
  unfold tailWord_434532
  simp only [CollatzResearch.WordTrace]
  refine ⟨7924342030886125501188925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10565789374514834001585233 7924342030886125501188925)
  ·
    refine ⟨2971628261582297062945847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7924342030886125501188925 2971628261582297062945847)
    ·
      refine ⟨4457442392373445594418771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2971628261582297062945847 4457442392373445594418771)
      ·
        refine ⟨6686163588560168391628157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4457442392373445594418771 6686163588560168391628157)
        ·
          refine ⟨2507311345710063146860559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6686163588560168391628157 2507311345710063146860559)
          ·
            refine ⟨3760967018565094720290839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2507311345710063146860559 3760967018565094720290839)
            ·
              refine ⟨5641450527847642080436259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3760967018565094720290839 5641450527847642080436259)
              ·
                refine ⟨8462175791771463120654389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5641450527847642080436259 8462175791771463120654389)
                ·
                  refine ⟨793328980478574667561349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8462175791771463120654389 793328980478574667561349)
                  ·
                    refine ⟨148749183839732750167753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 793328980478574667561349 148749183839732750167753)
                    ·
                      rfl

theorem cell22_434532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_434532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_434532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_434532 prefixEnd_434532 := by exact prefixLift 434532
  have htrace : WordTrace (prefixWord ++ tailWord_434532) baseStart_434532 baseEnd_434532 := by
    simpa [prefixWord, tailWord_434532, baseEnd_434532] using wordTrace_append hprefix tailTrace_434532
  have hstable : (prefixWord ++ tailWord_434532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434532).length < 2 ^ (prefixWord ++ tailWord_434532).sum := by decide
  have hdescent : baseEnd_434532 < baseStart_434532 := by decide
  rcases family_descends (prefixWord ++ tailWord_434532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434549 : List Nat := [1, 3, 4, 1, 2, 1, 2, 1, 3, 4]
def baseStart_434549 : Nat := 118140960795 + 434549 * 2 ^ 59
def prefixEnd_434549 : Nat := 4983230072969 + 3 ^ 40 * 434549 * 2
def baseEnd_434549 : Nat := 148755003287150372492701

theorem tailTrace_434549 : CollatzResearch.WordTrace tailWord_434549 prefixEnd_434549 148755003287150372492701 := by
  unfold tailWord_434549
  simp only [CollatzResearch.WordTrace]
  refine ⟨15849304102710662905746701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10566202735140441937164467 15849304102710662905746701)
  ·
    refine ⟨5943489038516498589655013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15849304102710662905746701 5943489038516498589655013)
    ·
      refine ⟨1114404194721843485560315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5943489038516498589655013 1114404194721843485560315)
      ·
        refine ⟨1671606292082765228340473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1114404194721843485560315 1671606292082765228340473)
        ·
          refine ⟨1253704719062073921255355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1671606292082765228340473 1253704719062073921255355)
          ·
            refine ⟨1880557078593110881883033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1253704719062073921255355 1880557078593110881883033)
            ·
              refine ⟨1410417808944833161412275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1880557078593110881883033 1410417808944833161412275)
              ·
                refine ⟨2115626713417249742118413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1410417808944833161412275 2115626713417249742118413)
                ·
                  refine ⟨793360017531468653294405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2115626713417249742118413 793360017531468653294405)
                  ·
                    refine ⟨148755003287150372492701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 793360017531468653294405 148755003287150372492701)
                    ·
                      rfl

theorem cell22_434549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_434549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_434549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_434549 prefixEnd_434549 := by exact prefixLift 434549
  have htrace : WordTrace (prefixWord ++ tailWord_434549) baseStart_434549 baseEnd_434549 := by
    simpa [prefixWord, tailWord_434549, baseEnd_434549] using wordTrace_append hprefix tailTrace_434549
  have hstable : (prefixWord ++ tailWord_434549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434549).length < 2 ^ (prefixWord ++ tailWord_434549).sum := by decide
  have hdescent : baseEnd_434549 < baseStart_434549 := by decide
  rcases family_descends (prefixWord ++ tailWord_434549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434609 : List Nat := [1, 2, 2, 4, 1, 2, 4, 6]
def baseStart_434609 : Nat := 118140960795 + 434609 * 2 ^ 59
def prefixEnd_434609 : Nat := 4983230072969 + 3 ^ 40 * 434609 * 2
def baseEnd_434609 : Nat := 16530615834814468443613

theorem tailTrace_434609 : CollatzResearch.WordTrace tailWord_434609 prefixEnd_434609 16530615834814468443613 := by
  unfold tailWord_434609
  simp only [CollatzResearch.WordTrace]
  refine ⟨15851492482493293152930881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10567661654995528768620587 15851492482493293152930881)
  ·
    refine ⟨11888619361869969864698161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15851492482493293152930881 11888619361869969864698161)
    ·
      refine ⟨8916464521402477398523621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11888619361869969864698161 8916464521402477398523621)
      ·
        refine ⟨1671837097762964512223179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8916464521402477398523621 1671837097762964512223179)
        ·
          refine ⟨2507755646644446768334769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1671837097762964512223179 2507755646644446768334769)
          ·
            refine ⟨1880816734983335076251077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2507755646644446768334769 1880816734983335076251077)
            ·
              refine ⟨352653137809375326797077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1880816734983335076251077 352653137809375326797077)
              ·
                refine ⟨16530615834814468443613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 352653137809375326797077 16530615834814468443613)
                ·
                  rfl

theorem cell22_434609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4, 6].length) (baseStart_434609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_434609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_434609 prefixEnd_434609 := by exact prefixLift 434609
  have htrace : WordTrace (prefixWord ++ tailWord_434609) baseStart_434609 baseEnd_434609 := by
    simpa [prefixWord, tailWord_434609, baseEnd_434609] using wordTrace_append hprefix tailTrace_434609
  have hstable : (prefixWord ++ tailWord_434609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434609).length < 2 ^ (prefixWord ++ tailWord_434609).sum := by decide
  have hdescent : baseEnd_434609 < baseStart_434609 := by decide
  rcases family_descends (prefixWord ++ tailWord_434609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434641 : List Nat := [1, 2, 2, 1, 2, 1, 1, 8, 1, 3]
def baseStart_434641 : Nat := 118140960795 + 434641 * 2 ^ 59
def prefixEnd_434641 : Nat := 4983230072969 + 3 ^ 40 * 434641 * 2
def baseEnd_434641 : Nat := 148786496767292799192419

theorem tailTrace_434641 : CollatzResearch.WordTrace tailWord_434641 prefixEnd_434641 148786496767292799192419 := by
  unfold tailWord_434641
  simp only [CollatzResearch.WordTrace]
  refine ⟨15852659618377362618095777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10568439745584908412063851 15852659618377362618095777)
  ·
    refine ⟨11889494713783021963571833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15852659618377362618095777 11889494713783021963571833)
    ·
      refine ⟨8917121035337266472678875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11889494713783021963571833 8917121035337266472678875)
      ·
        refine ⟨13375681553005899709018313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8917121035337266472678875 13375681553005899709018313)
        ·
          refine ⟨10031761164754424781763735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13375681553005899709018313 10031761164754424781763735)
          ·
            refine ⟨15047641747131637172645603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10031761164754424781763735 15047641747131637172645603)
            ·
              refine ⟨22571462620697455758968405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15047641747131637172645603 22571462620697455758968405)
              ·
                refine ⟨264509327586298309675411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 22571462620697455758968405 264509327586298309675411)
                ·
                  refine ⟨396763991379447464513117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 264509327586298309675411 396763991379447464513117)
                  ·
                    refine ⟨148786496767292799192419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 396763991379447464513117 148786496767292799192419)
                    ·
                      rfl

theorem cell22_434641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 8, 1, 3].length) (baseStart_434641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_434641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_434641 prefixEnd_434641 := by exact prefixLift 434641
  have htrace : WordTrace (prefixWord ++ tailWord_434641) baseStart_434641 baseEnd_434641 := by
    simpa [prefixWord, tailWord_434641, baseEnd_434641] using wordTrace_append hprefix tailTrace_434641
  have hstable : (prefixWord ++ tailWord_434641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434641).length < 2 ^ (prefixWord ++ tailWord_434641).sum := by decide
  have hdescent : baseEnd_434641 < baseStart_434641 := by decide
  rcases family_descends (prefixWord ++ tailWord_434641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434682 : List Nat := [3, 1, 1, 1, 1, 2, 2, 1, 10]
def baseStart_434682 : Nat := 118140960795 + 434682 * 2 ^ 59
def prefixEnd_434682 : Nat := 4983230072969 + 3 ^ 40 * 434682 * 2
def baseEnd_434682 : Nat := 49600177301727452972431

theorem tailTrace_434682 : CollatzResearch.WordTrace tailWord_434682 prefixEnd_434682 49600177301727452972431 := by
  unfold tailWord_434682
  simp only [CollatzResearch.WordTrace]
  refine ⟨3963538752807206655084575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10569436674152551080225533 3963538752807206655084575)
  ·
    refine ⟨5945308129210809982626863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3963538752807206655084575 5945308129210809982626863)
    ·
      refine ⟨8917962193816214973940295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5945308129210809982626863 8917962193816214973940295)
      ·
        refine ⟨13376943290724322460910443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8917962193816214973940295 13376943290724322460910443)
        ·
          refine ⟨20065414936086483691365665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13376943290724322460910443 20065414936086483691365665)
          ·
            refine ⟨15049061202064862768524249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20065414936086483691365665 15049061202064862768524249)
            ·
              refine ⟨11286795901548647076393187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15049061202064862768524249 11286795901548647076393187)
              ·
                refine ⟨16930193852322970614589781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11286795901548647076393187 16930193852322970614589781)
                ·
                  refine ⟨49600177301727452972431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 16930193852322970614589781 49600177301727452972431)
                  ·
                    rfl

theorem cell22_434682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 10].length) (baseStart_434682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_434682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_434682 prefixEnd_434682 := by exact prefixLift 434682
  have htrace : WordTrace (prefixWord ++ tailWord_434682) baseStart_434682 baseEnd_434682 := by
    simpa [prefixWord, tailWord_434682, baseEnd_434682] using wordTrace_append hprefix tailTrace_434682
  have hstable : (prefixWord ++ tailWord_434682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434682).length < 2 ^ (prefixWord ++ tailWord_434682).sum := by decide
  have hdescent : baseEnd_434682 < baseStart_434682 := by decide
  rcases family_descends (prefixWord ++ tailWord_434682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434692 : List Nat := [2, 3, 2, 3, 1, 3, 2, 2, 1, 3]
def baseStart_434692 : Nat := 118140960795 + 434692 * 2 ^ 59
def prefixEnd_434692 : Nat := 4983230072969 + 3 ^ 40 * 434692 * 2
def baseEnd_434692 : Nat := 148803955109545666167263

theorem tailTrace_434692 : CollatzResearch.WordTrace tailWord_434692 prefixEnd_434692 148803955109545666167263 := by
  unfold tailWord_434692
  simp only [CollatzResearch.WordTrace]
  refine ⟨7927259870596299164101165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10569679827461732218801553 7927259870596299164101165)
  ·
    refine ⟨2972722451473612186537937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7927259870596299164101165 2972722451473612186537937)
    ·
      refine ⟨2229541838605209139903453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2972722451473612186537937 2229541838605209139903453)
      ·
        refine ⟨836078189476953427463795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2229541838605209139903453 836078189476953427463795)
        ·
          refine ⟨1254117284215430141195693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 836078189476953427463795 1254117284215430141195693)
          ·
            refine ⟨470293981580786302948385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1254117284215430141195693 470293981580786302948385)
            ·
              refine ⟨352720486185589727211289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 470293981580786302948385 352720486185589727211289)
              ·
                refine ⟨264540364639192295408467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 352720486185589727211289 264540364639192295408467)
                ·
                  refine ⟨396810546958788443112701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 264540364639192295408467 396810546958788443112701)
                  ·
                    refine ⟨148803955109545666167263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 396810546958788443112701 148803955109545666167263)
                    ·
                      rfl

theorem cell22_434692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2, 2, 1, 3].length) (baseStart_434692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_434692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_434692 prefixEnd_434692 := by exact prefixLift 434692
  have htrace : WordTrace (prefixWord ++ tailWord_434692) baseStart_434692 baseEnd_434692 := by
    simpa [prefixWord, tailWord_434692, baseEnd_434692] using wordTrace_append hprefix tailTrace_434692
  have hstable : (prefixWord ++ tailWord_434692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434692).length < 2 ^ (prefixWord ++ tailWord_434692).sum := by decide
  have hdescent : baseEnd_434692 < baseStart_434692 := by decide
  rcases family_descends (prefixWord ++ tailWord_434692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434714 : List Nat := [3, 1, 1, 3, 1, 1, 3, 3, 1, 5]
def baseStart_434714 : Nat := 118140960795 + 434714 * 2 ^ 59
def prefixEnd_434714 : Nat := 4983230072969 + 3 ^ 40 * 434714 * 2
def baseEnd_434714 : Nat := 148811486159144942117195

theorem tailTrace_434714 : CollatzResearch.WordTrace tailWord_434714 prefixEnd_434714 148811486159144942117195 := by
  unfold tailWord_434714
  simp only [CollatzResearch.WordTrace]
  refine ⟨3963830536778224021375799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10570214764741930723668797 3963830536778224021375799)
  ·
    refine ⟨5945745805167336032063699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3963830536778224021375799 5945745805167336032063699)
    ·
      refine ⟨8918618707751004048095549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5945745805167336032063699 8918618707751004048095549)
      ·
        refine ⟨3344482015406626518035831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8918618707751004048095549 3344482015406626518035831)
        ·
          refine ⟨5016723023109939777053747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3344482015406626518035831 5016723023109939777053747)
          ·
            refine ⟨7525084534664909665580621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5016723023109939777053747 7525084534664909665580621)
            ·
              refine ⟨2821906700499341124592733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7525084534664909665580621 2821906700499341124592733)
              ·
                refine ⟨1058215012687252921722275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2821906700499341124592733 1058215012687252921722275)
                ·
                  refine ⟨1587322519030879382583413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1058215012687252921722275 1587322519030879382583413)
                  ·
                    refine ⟨148811486159144942117195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1587322519030879382583413 148811486159144942117195)
                    ·
                      rfl

theorem cell22_434714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 1, 5].length) (baseStart_434714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_434714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_434714 prefixEnd_434714 := by exact prefixLift 434714
  have htrace : WordTrace (prefixWord ++ tailWord_434714) baseStart_434714 baseEnd_434714 := by
    simpa [prefixWord, tailWord_434714, baseEnd_434714] using wordTrace_append hprefix tailTrace_434714
  have hstable : (prefixWord ++ tailWord_434714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434714).length < 2 ^ (prefixWord ++ tailWord_434714).sum := by decide
  have hdescent : baseEnd_434714 < baseStart_434714 := by decide
  rcases family_descends (prefixWord ++ tailWord_434714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434748 : List Nat := [2, 2, 2, 2, 3, 1, 3, 2, 2, 3]
def baseStart_434748 : Nat := 118140960795 + 434748 * 2 ^ 59
def prefixEnd_434748 : Nat := 4983230072969 + 3 ^ 40 * 434748 * 2
def baseEnd_434748 : Nat := 148823125053980186767091

theorem tailTrace_434748 : CollatzResearch.WordTrace tailWord_434748 prefixEnd_434748 148823125053980186767091 := by
  unfold tailWord_434748
  simp only [CollatzResearch.WordTrace]
  refine ⟨7928281114494859946120449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10571041485993146594827265 7928281114494859946120449)
  ·
    refine ⟨5946210835871144959590337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7928281114494859946120449 5946210835871144959590337)
    ·
      refine ⟨4459658126903358719692753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5946210835871144959590337 4459658126903358719692753)
      ·
        refine ⟨3344743595177519039769565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4459658126903358719692753 3344743595177519039769565)
        ·
          refine ⟨1254278848191569639913587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3344743595177519039769565 1254278848191569639913587)
          ·
            refine ⟨1881418272287354459870381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1254278848191569639913587 1881418272287354459870381)
            ·
              refine ⟨705531852107757922451393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1881418272287354459870381 705531852107757922451393)
              ·
                refine ⟨529148889080818441838545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 705531852107757922451393 529148889080818441838545)
                ·
                  refine ⟨396861666810613831378909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 529148889080818441838545 396861666810613831378909)
                  ·
                    refine ⟨148823125053980186767091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 396861666810613831378909 148823125053980186767091)
                    ·
                      rfl

theorem cell22_434748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 2, 2, 3].length) (baseStart_434748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_434748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_434748 prefixEnd_434748 := by exact prefixLift 434748
  have htrace : WordTrace (prefixWord ++ tailWord_434748) baseStart_434748 baseEnd_434748 := by
    simpa [prefixWord, tailWord_434748, baseEnd_434748] using wordTrace_append hprefix tailTrace_434748
  have hstable : (prefixWord ++ tailWord_434748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434748).length < 2 ^ (prefixWord ++ tailWord_434748).sum := by decide
  have hdescent : baseEnd_434748 < baseStart_434748 := by decide
  rcases family_descends (prefixWord ++ tailWord_434748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434776 : List Nat := [2, 1, 2, 2, 1, 2, 4, 2, 3, 3]
def baseStart_434776 : Nat := 118140960795 + 434776 * 2 ^ 59
def prefixEnd_434776 : Nat := 4983230072969 + 3 ^ 40 * 434776 * 2
def baseEnd_434776 : Nat := 148832710026197447067005

theorem tailTrace_434776 : CollatzResearch.WordTrace tailWord_434776 prefixEnd_434776 148832710026197447067005 := by
  unfold tailWord_434776
  simp only [CollatzResearch.WordTrace]
  refine ⟨7928791736444140337130091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10571722315258853782840121 7928791736444140337130091)
  ·
    refine ⟨11893187604666210505695137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7928791736444140337130091 11893187604666210505695137)
    ·
      refine ⟨8919890703499657879271353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11893187604666210505695137 8919890703499657879271353)
      ·
        refine ⟨6689918027624743409453515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8919890703499657879271353 6689918027624743409453515)
        ·
          refine ⟨10034877041437115114180273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6689918027624743409453515 10034877041437115114180273)
          ·
            refine ⟨7526157781077836335635205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10034877041437115114180273 7526157781077836335635205)
            ·
              refine ⟨1411154583952094312931601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7526157781077836335635205 1411154583952094312931601)
              ·
                refine ⟨1058365937964070734698701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1411154583952094312931601 1058365937964070734698701)
                ·
                  refine ⟨396887226736526525512013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1058365937964070734698701 396887226736526525512013)
                  ·
                    refine ⟨148832710026197447067005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 396887226736526525512013 148832710026197447067005)
                    ·
                      rfl

theorem cell22_434776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 2, 3, 3].length) (baseStart_434776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_434776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_434776 prefixEnd_434776 := by exact prefixLift 434776
  have htrace : WordTrace (prefixWord ++ tailWord_434776) baseStart_434776 baseEnd_434776 := by
    simpa [prefixWord, tailWord_434776, baseEnd_434776] using wordTrace_append hprefix tailTrace_434776
  have hstable : (prefixWord ++ tailWord_434776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434776).length < 2 ^ (prefixWord ++ tailWord_434776).sum := by decide
  have hdescent : baseEnd_434776 < baseStart_434776 := by decide
  rcases family_descends (prefixWord ++ tailWord_434776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434864 : List Nat := [2, 1, 1, 1, 2, 1, 3, 2, 3, 6]
def baseStart_434864 : Nat := 118140960795 + 434864 * 2 ^ 59
def prefixEnd_434864 : Nat := 4983230072969 + 3 ^ 40 * 434864 * 2
def baseEnd_434864 : Nat := 148862834224594550866735

theorem tailTrace_434864 : CollatzResearch.WordTrace tailWord_434864 prefixEnd_434864 148862834224594550866735 := by
  unfold tailWord_434864
  simp only [CollatzResearch.WordTrace]
  refine ⟨7930396548284735851731823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10573862064379647802309097 7930396548284735851731823)
  ·
    refine ⟨11895594822427103777597735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7930396548284735851731823 11895594822427103777597735)
    ·
      refine ⟨17843392233640655666396603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11895594822427103777597735 17843392233640655666396603)
      ·
        refine ⟨26765088350460983499594905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17843392233640655666396603 26765088350460983499594905)
        ·
          refine ⟨20073816262845737624696179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26765088350460983499594905 20073816262845737624696179)
          ·
            refine ⟨30110724394268606437044269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20073816262845737624696179 30110724394268606437044269)
            ·
              refine ⟨11291521647850727413891601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30110724394268606437044269 11291521647850727413891601)
              ·
                refine ⟨8468641235888045560418701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11291521647850727413891601 8468641235888045560418701)
                ·
                  refine ⟨3175740463458017085157013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8468641235888045560418701 3175740463458017085157013)
                  ·
                    refine ⟨148862834224594550866735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3175740463458017085157013 148862834224594550866735)
                    ·
                      rfl

theorem cell22_434864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 3, 6].length) (baseStart_434864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_434864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_434864 prefixEnd_434864 := by exact prefixLift 434864
  have htrace : WordTrace (prefixWord ++ tailWord_434864) baseStart_434864 baseEnd_434864 := by
    simpa [prefixWord, tailWord_434864, baseEnd_434864] using wordTrace_append hprefix tailTrace_434864
  have hstable : (prefixWord ++ tailWord_434864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434864).length < 2 ^ (prefixWord ++ tailWord_434864).sum := by decide
  have hdescent : baseEnd_434864 < baseStart_434864 := by decide
  rcases family_descends (prefixWord ++ tailWord_434864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434898 : List Nat := [3, 2, 2, 2, 3, 1, 1, 1, 1, 6]
def baseStart_434898 : Nat := 118140960795 + 434898 * 2 ^ 59
def prefixEnd_434898 : Nat := 4983230072969 + 3 ^ 40 * 434898 * 2
def baseEnd_434898 : Nat := 148874473119429795516631

theorem tailTrace_434898 : CollatzResearch.WordTrace tailWord_434898 prefixEnd_434898 148874473119429795516631 := by
  unfold tailWord_434898
  simp only [CollatzResearch.WordTrace]
  refine ⟨3965508294611573877550337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10574688785630863673467565 3965508294611573877550337)
  ·
    refine ⟨2974131220958680408162753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3965508294611573877550337 2974131220958680408162753)
    ·
      refine ⟨2230598415719010306122065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2974131220958680408162753 2230598415719010306122065)
      ·
        refine ⟨1672948811789257729591549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2230598415719010306122065 1672948811789257729591549)
        ·
          refine ⟨627355804420971648596831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1672948811789257729591549 627355804420971648596831)
          ·
            refine ⟨941033706631457472895247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 627355804420971648596831 941033706631457472895247)
            ·
              refine ⟨1411550559947186209342871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 941033706631457472895247 1411550559947186209342871)
              ·
                refine ⟨2117325839920779314014307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1411550559947186209342871 2117325839920779314014307)
                ·
                  refine ⟨3175988759881168971021461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2117325839920779314014307 3175988759881168971021461)
                  ·
                    refine ⟨148874473119429795516631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3175988759881168971021461 148874473119429795516631)
                    ·
                      rfl

theorem cell22_434898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_434898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_434898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_434898 prefixEnd_434898 := by exact prefixLift 434898
  have htrace : WordTrace (prefixWord ++ tailWord_434898) baseStart_434898 baseEnd_434898 := by
    simpa [prefixWord, tailWord_434898, baseEnd_434898] using wordTrace_append hprefix tailTrace_434898
  have hstable : (prefixWord ++ tailWord_434898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434898).length < 2 ^ (prefixWord ++ tailWord_434898).sum := by decide
  have hdescent : baseEnd_434898 < baseStart_434898 := by decide
  rcases family_descends (prefixWord ++ tailWord_434898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434928 : List Nat := [2, 1, 1, 1, 3, 1, 6, 1, 3, 3]
def baseStart_434928 : Nat := 118140960795 + 434928 * 2 ^ 59
def prefixEnd_434928 : Nat := 4983230072969 + 3 ^ 40 * 434928 * 2
def baseEnd_434928 : Nat := 148884742732519717266539

theorem tailTrace_434928 : CollatzResearch.WordTrace tailWord_434928 prefixEnd_434928 148884742732519717266539 := by
  unfold tailWord_434928
  simp only [CollatzResearch.WordTrace]
  refine ⟨7931563684168805316896719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10575418245558407089195625 7931563684168805316896719)
  ·
    refine ⟨11897345526253207975345079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7931563684168805316896719 11897345526253207975345079)
    ·
      refine ⟨17846018289379811963017619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11897345526253207975345079 17846018289379811963017619)
      ·
        refine ⟨26769027434069717944526429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17846018289379811963017619 26769027434069717944526429)
        ·
          refine ⟨10038385287776144229197411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26769027434069717944526429 10038385287776144229197411)
          ·
            refine ⟨15057577931664216343796117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10038385287776144229197411 15057577931664216343796117)
            ·
              refine ⟨705823965546760141115443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15057577931664216343796117 705823965546760141115443)
              ·
                refine ⟨1058735948320140211673165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 705823965546760141115443 1058735948320140211673165)
                ·
                  refine ⟨397025980620052579377437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1058735948320140211673165 397025980620052579377437)
                  ·
                    refine ⟨148884742732519717266539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 397025980620052579377437 148884742732519717266539)
                    ·
                      rfl

theorem cell22_434928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 1, 3, 3].length) (baseStart_434928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_434928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_434928 prefixEnd_434928 := by exact prefixLift 434928
  have htrace : WordTrace (prefixWord ++ tailWord_434928) baseStart_434928 baseEnd_434928 := by
    simpa [prefixWord, tailWord_434928, baseEnd_434928] using wordTrace_append hprefix tailTrace_434928
  have hstable : (prefixWord ++ tailWord_434928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434928).length < 2 ^ (prefixWord ++ tailWord_434928).sum := by decide
  have hdescent : baseEnd_434928 < baseStart_434928 := by decide
  rcases family_descends (prefixWord ++ tailWord_434928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435005 : List Nat := [1, 4, 1, 4, 2, 1, 1, 1, 3, 4]
def baseStart_435005 : Nat := 118140960795 + 435005 * 2 ^ 59
def prefixEnd_435005 : Nat := 4983230072969 + 3 ^ 40 * 435005 * 2
def baseEnd_435005 : Nat := 148911101406117183091303

theorem tailTrace_435005 : CollatzResearch.WordTrace tailWord_435005 prefixEnd_435005 148911101406117183091303 := by
  unfold tailWord_435005
  simp only [CollatzResearch.WordTrace]
  refine ⟨15865935789058652784346469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10577290526039101856230979 15865935789058652784346469)
  ·
    refine ⟨2974862960448497397064963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15865935789058652784346469 2974862960448497397064963)
    ·
      refine ⟨4462294440672746095597445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2974862960448497397064963 4462294440672746095597445)
      ·
        refine ⟨836680207626139892924521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4462294440672746095597445 836680207626139892924521)
        ·
          refine ⟨627510155719604919693391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 836680207626139892924521 627510155719604919693391)
          ·
            refine ⟨941265233579407379540087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 627510155719604919693391 941265233579407379540087)
            ·
              refine ⟨1411897850369111069310131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 941265233579407379540087 1411897850369111069310131)
              ·
                refine ⟨2117846775553666603965197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1411897850369111069310131 2117846775553666603965197)
                ·
                  refine ⟨794192540832624976486949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2117846775553666603965197 794192540832624976486949)
                  ·
                    refine ⟨148911101406117183091303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 794192540832624976486949 148911101406117183091303)
                    ·
                      rfl

theorem cell22_435005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 3, 4].length) (baseStart_435005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_435005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_435005 prefixEnd_435005 := by exact prefixLift 435005
  have htrace : WordTrace (prefixWord ++ tailWord_435005) baseStart_435005 baseEnd_435005 := by
    simpa [prefixWord, tailWord_435005, baseEnd_435005] using wordTrace_append hprefix tailTrace_435005
  have hstable : (prefixWord ++ tailWord_435005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435005).length < 2 ^ (prefixWord ++ tailWord_435005).sum := by decide
  have hdescent : baseEnd_435005 < baseStart_435005 := by decide
  rcases family_descends (prefixWord ++ tailWord_435005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435018 : List Nat := [3, 1, 2, 1, 1, 1, 2, 4, 4, 3]
def baseStart_435018 : Nat := 118140960795 + 435018 * 2 ^ 59
def prefixEnd_435018 : Nat := 4983230072969 + 3 ^ 40 * 435018 * 2
def baseEnd_435018 : Nat := 148915551571789482516263

theorem tailTrace_435018 : CollatzResearch.WordTrace tailWord_435018 prefixEnd_435018 148915551571789482516263 := by
  unfold tailWord_435018
  simp only [CollatzResearch.WordTrace]
  refine ⟨3966602484502889001142427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10577606625341037336379805 3966602484502889001142427)
  ·
    refine ⟨5949903726754333501713641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3966602484502889001142427 5949903726754333501713641)
    ·
      refine ⟨4462427795065750126285231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5949903726754333501713641 4462427795065750126285231)
      ·
        refine ⟨6693641692598625189427847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4462427795065750126285231 6693641692598625189427847)
        ·
          refine ⟨10040462538897937784141771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6693641692598625189427847 10040462538897937784141771)
          ·
            refine ⟨15060693808346906676212657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10040462538897937784141771 15060693808346906676212657)
            ·
              refine ⟨11295520356260180007159493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15060693808346906676212657 11295520356260180007159493)
              ·
                refine ⟨2117910066798783751342405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11295520356260180007159493 2117910066798783751342405)
                ·
                  refine ⟨397108137524771953376701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2117910066798783751342405 397108137524771953376701)
                  ·
                    refine ⟨148915551571789482516263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 397108137524771953376701 148915551571789482516263)
                    ·
                      rfl

theorem cell22_435018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 4, 3].length) (baseStart_435018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_435018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_435018 prefixEnd_435018 := by exact prefixLift 435018
  have htrace : WordTrace (prefixWord ++ tailWord_435018) baseStart_435018 baseEnd_435018 := by
    simpa [prefixWord, tailWord_435018, baseEnd_435018] using wordTrace_append hprefix tailTrace_435018
  have hstable : (prefixWord ++ tailWord_435018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435018).length < 2 ^ (prefixWord ++ tailWord_435018).sum := by decide
  have hdescent : baseEnd_435018 < baseStart_435018 := by decide
  rcases family_descends (prefixWord ++ tailWord_435018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435031 : List Nat := [1, 1, 3, 2, 4, 11]
def baseStart_435031 : Nat := 118140960795 + 435031 * 2 ^ 59
def prefixEnd_435031 : Nat := 4983230072969 + 3 ^ 40 * 435031 * 2
def baseEnd_435031 : Nat := 1838518539968663974583

theorem tailTrace_435031 : CollatzResearch.WordTrace tailWord_435031 prefixEnd_435031 1838518539968663974583 := by
  unfold tailWord_435031
  simp only [CollatzResearch.WordTrace]
  refine ⟨15866884086964459224792947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10577922724642972816528631 15866884086964459224792947)
  ·
    refine ⟨23800326130446688837189421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15866884086964459224792947 23800326130446688837189421)
    ·
      refine ⟨8925122298917508313946033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23800326130446688837189421 8925122298917508313946033)
      ·
        refine ⟨6693841724188131235459525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8925122298917508313946033 6693841724188131235459525)
        ·
          refine ⟨1255095323285274606648661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6693841724188131235459525 1255095323285274606648661)
          ·
            refine ⟨1838518539968663974583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 1255095323285274606648661 1838518539968663974583)
            ·
              rfl

theorem cell22_435031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 11].length) (baseStart_435031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_435031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_435031 prefixEnd_435031 := by exact prefixLift 435031
  have htrace : WordTrace (prefixWord ++ tailWord_435031) baseStart_435031 baseEnd_435031 := by
    simpa [prefixWord, tailWord_435031, baseEnd_435031] using wordTrace_append hprefix tailTrace_435031
  have hstable : (prefixWord ++ tailWord_435031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435031).length < 2 ^ (prefixWord ++ tailWord_435031).sum := by decide
  have hdescent : baseEnd_435031 < baseStart_435031 := by decide
  rcases family_descends (prefixWord ++ tailWord_435031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435033 : List Nat := [1, 2, 1, 2, 2, 4, 2, 2, 2, 4]
def baseStart_435033 : Nat := 118140960795 + 435033 * 2 ^ 59
def prefixEnd_435033 : Nat := 4983230072969 + 3 ^ 40 * 435033 * 2
def baseEnd_435033 : Nat := 148920686378334443391217

theorem tailTrace_435033 : CollatzResearch.WordTrace tailWord_435033 prefixEnd_435033 148920686378334443391217 := by
  unfold tailWord_435033
  simp only [CollatzResearch.WordTrace]
  refine ⟨15866957032957213566365753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10577971355304809044243835 15866957032957213566365753)
  ·
    refine ⟨11900217774717910174774315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15866957032957213566365753 11900217774717910174774315)
    ·
      refine ⟨17850326662076865262161473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11900217774717910174774315 17850326662076865262161473)
      ·
        refine ⟨13387744996557648946621105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17850326662076865262161473 13387744996557648946621105)
        ·
          refine ⟨10040808747418236709965829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13387744996557648946621105 10040808747418236709965829)
          ·
            refine ⟨1882651640140919383118593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10040808747418236709965829 1882651640140919383118593)
            ·
              refine ⟨1411988730105689537338945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1882651640140919383118593 1411988730105689537338945)
              ·
                refine ⟨1058991547579267153004209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1411988730105689537338945 1058991547579267153004209)
                ·
                  refine ⟨794243660684450364753157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1058991547579267153004209 794243660684450364753157)
                  ·
                    refine ⟨148920686378334443391217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 794243660684450364753157 148920686378334443391217)
                    ·
                      rfl

theorem cell22_435033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 2, 2, 4].length) (baseStart_435033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_435033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_435033 prefixEnd_435033 := by exact prefixLift 435033
  have htrace : WordTrace (prefixWord ++ tailWord_435033) baseStart_435033 baseEnd_435033 := by
    simpa [prefixWord, tailWord_435033, baseEnd_435033] using wordTrace_append hprefix tailTrace_435033
  have hstable : (prefixWord ++ tailWord_435033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435033).length < 2 ^ (prefixWord ++ tailWord_435033).sum := by decide
  have hdescent : baseEnd_435033 < baseStart_435033 := by decide
  rcases family_descends (prefixWord ++ tailWord_435033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435048 : List Nat := [2, 1, 4, 2, 1, 2, 3, 7]
def baseStart_435048 : Nat := 118140960795 + 435048 * 2 ^ 59
def prefixEnd_435048 : Nat := 4983230072969 + 3 ^ 40 * 435048 * 2
def baseEnd_435048 : Nat := 16547313464986600474019

theorem tailTrace_435048 : CollatzResearch.WordTrace tailWord_435048 prefixEnd_435048 16547313464986600474019 := by
  unfold tailWord_435048
  simp only [CollatzResearch.WordTrace]
  refine ⟨7933752063951435564080899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10578336085268580752107865 7933752063951435564080899)
  ·
    refine ⟨11900628095927153346121349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7933752063951435564080899 11900628095927153346121349)
    ·
      refine ⟨2231367767986341252397753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11900628095927153346121349 2231367767986341252397753)
      ·
        refine ⟨1673525825989755939298315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2231367767986341252397753 1673525825989755939298315)
        ·
          refine ⟨2510288738984633908947473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1673525825989755939298315 2510288738984633908947473)
          ·
            refine ⟨1882716554238475431710605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2510288738984633908947473 1882716554238475431710605)
            ·
              refine ⟨706018707839428286891477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1882716554238475431710605 706018707839428286891477)
              ·
                refine ⟨16547313464986600474019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 706018707839428286891477 16547313464986600474019)
                ·
                  rfl

theorem cell22_435048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 7].length) (baseStart_435048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_435048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_435048 prefixEnd_435048 := by exact prefixLift 435048
  have htrace : WordTrace (prefixWord ++ tailWord_435048) baseStart_435048 baseEnd_435048 := by
    simpa [prefixWord, tailWord_435048, baseEnd_435048] using wordTrace_append hprefix tailTrace_435048
  have hstable : (prefixWord ++ tailWord_435048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435048).length < 2 ^ (prefixWord ++ tailWord_435048).sum := by decide
  have hdescent : baseEnd_435048 < baseStart_435048 := by decide
  rcases family_descends (prefixWord ++ tailWord_435048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435093 : List Nat := [1, 3, 2, 1, 1, 5, 1, 1, 7]
def baseStart_435093 : Nat := 118140960795 + 435093 * 2 ^ 59
def prefixEnd_435093 : Nat := 4983230072969 + 3 ^ 40 * 435093 * 2
def baseEnd_435093 : Nat := 49647075201504762297011

theorem tailTrace_435093 : CollatzResearch.WordTrace tailWord_435093 prefixEnd_435093 49647075201504762297011 := by
  unfold tailWord_435093
  simp only [CollatzResearch.WordTrace]
  refine ⟨15869145412739843813549933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10579430275159895875699955 15869145412739843813549933)
  ·
    refine ⟨5950929529777441430081225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15869145412739843813549933 5950929529777441430081225)
    ·
      refine ⟨4463197147333081072560919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5950929529777441430081225 4463197147333081072560919)
      ·
        refine ⟨6694795720999621608841379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4463197147333081072560919 6694795720999621608841379)
        ·
          refine ⟨10042193581499432413262069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6694795720999621608841379 10042193581499432413262069)
          ·
            refine ⟨941455648265571788743319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10042193581499432413262069 941455648265571788743319)
            ·
              refine ⟨1412183472398357683114979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 941455648265571788743319 1412183472398357683114979)
              ·
                refine ⟨2118275208597536524672469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1412183472398357683114979 2118275208597536524672469)
                ·
                  refine ⟨49647075201504762297011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2118275208597536524672469 49647075201504762297011)
                  ·
                    rfl

theorem cell22_435093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 7].length) (baseStart_435093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_435093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_435093 prefixEnd_435093 := by exact prefixLift 435093
  have htrace : WordTrace (prefixWord ++ tailWord_435093) baseStart_435093 baseEnd_435093 := by
    simpa [prefixWord, tailWord_435093, baseEnd_435093] using wordTrace_append hprefix tailTrace_435093
  have hstable : (prefixWord ++ tailWord_435093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435093).length < 2 ^ (prefixWord ++ tailWord_435093).sum := by decide
  have hdescent : baseEnd_435093 < baseStart_435093 := by decide
  rcases family_descends (prefixWord ++ tailWord_435093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435108 : List Nat := [2, 3, 1, 2, 1, 2, 1, 3, 2, 5]
def baseStart_435108 : Nat := 118140960795 + 435108 * 2 ^ 59
def prefixEnd_435108 : Nat := 4983230072969 + 3 ^ 40 * 435108 * 2
def baseEnd_435108 : Nat := 148946360411059247765987

theorem tailTrace_435108 : CollatzResearch.WordTrace tailWord_435108 prefixEnd_435108 148946360411059247765987 := by
  unfold tailWord_435108
  simp only [CollatzResearch.WordTrace]
  refine ⟨7934846253842750687672989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10579795005123667583563985 7934846253842750687672989)
  ·
    refine ⟨2975567345191031507877371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7934846253842750687672989 2975567345191031507877371)
    ·
      refine ⟨4463351017786547261816057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2975567345191031507877371 4463351017786547261816057)
      ·
        refine ⟨3347513263339910446362043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4463351017786547261816057 3347513263339910446362043)
        ·
          refine ⟨5021269895009865669543065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3347513263339910446362043 5021269895009865669543065)
          ·
            refine ⟨3765952421257399252157299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5021269895009865669543065 3765952421257399252157299)
            ·
              refine ⟨5648928631886098878235949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3765952421257399252157299 5648928631886098878235949)
              ·
                refine ⟨2118348236957287079338481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5648928631886098878235949 2118348236957287079338481)
                ·
                  refine ⟨1588761177717965309503861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2118348236957287079338481 1588761177717965309503861)
                  ·
                    refine ⟨148946360411059247765987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1588761177717965309503861 148946360411059247765987)
                    ·
                      rfl

theorem cell22_435108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_435108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_435108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_435108 prefixEnd_435108 := by exact prefixLift 435108
  have htrace : WordTrace (prefixWord ++ tailWord_435108) baseStart_435108 baseEnd_435108 := by
    simpa [prefixWord, tailWord_435108, baseEnd_435108] using wordTrace_append hprefix tailTrace_435108
  have hstable : (prefixWord ++ tailWord_435108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435108).length < 2 ^ (prefixWord ++ tailWord_435108).sum := by decide
  have hdescent : baseEnd_435108 < baseStart_435108 := by decide
  rcases family_descends (prefixWord ++ tailWord_435108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435183 : List Nat := [1, 1, 2, 1, 4, 3, 2, 8]
def baseStart_435183 : Nat := 118140960795 + 435183 * 2 ^ 59
def prefixEnd_435183 : Nat := 4983230072969 + 3 ^ 40 * 435183 * 2
def baseEnd_435183 : Nat := 16552448271531561348973

theorem tailTrace_435183 : CollatzResearch.WordTrace tailWord_435183 prefixEnd_435183 16552448271531561348973 := by
  unfold tailWord_435183
  simp only [CollatzResearch.WordTrace]
  refine ⟨15872427982413789184326203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10581618654942526122884135 15872427982413789184326203)
  ·
    refine ⟨23808641973620683776489305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15872427982413789184326203 23808641973620683776489305)
    ·
      refine ⟨17856481480215512832366979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23808641973620683776489305 17856481480215512832366979)
      ·
        refine ⟨26784722220323269248550469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17856481480215512832366979 26784722220323269248550469)
        ·
          refine ⟨5022135416310612984103213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26784722220323269248550469 5022135416310612984103213)
          ·
            refine ⟨1883300781116479869038705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5022135416310612984103213 1883300781116479869038705)
            ·
              refine ⟨1412475585837359901779029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1883300781116479869038705 1412475585837359901779029)
              ·
                refine ⟨16552448271531561348973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1412475585837359901779029 16552448271531561348973)
                ·
                  rfl

theorem cell22_435183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 8].length) (baseStart_435183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_435183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_435183 prefixEnd_435183 := by exact prefixLift 435183
  have htrace : WordTrace (prefixWord ++ tailWord_435183) baseStart_435183 baseEnd_435183 := by
    simpa [prefixWord, tailWord_435183, baseEnd_435183] using wordTrace_append hprefix tailTrace_435183
  have hstable : (prefixWord ++ tailWord_435183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435183).length < 2 ^ (prefixWord ++ tailWord_435183).sum := by decide
  have hdescent : baseEnd_435183 < baseStart_435183 := by decide
  rcases family_descends (prefixWord ++ tailWord_435183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435185 : List Nat := [1, 2, 2, 2, 4, 1, 1, 3, 2, 4]
def baseStart_435185 : Nat := 118140960795 + 435185 * 2 ^ 59
def prefixEnd_435185 : Nat := 4983230072969 + 3 ^ 40 * 435185 * 2
def baseEnd_435185 : Nat := 148972719084656713590751

theorem tailTrace_435185 : CollatzResearch.WordTrace tailWord_435185 prefixEnd_435185 148972719084656713590751 := by
  unfold tailWord_435185
  simp only [CollatzResearch.WordTrace]
  refine ⟨15872500928406543525899009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10581667285604362350599339 15872500928406543525899009)
  ·
    refine ⟨11904375696304907644424257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15872500928406543525899009 11904375696304907644424257)
    ·
      refine ⟨8928281772228680733318193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11904375696304907644424257 8928281772228680733318193)
      ·
        refine ⟨6696211329171510549988645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8928281772228680733318193 6696211329171510549988645)
        ·
          refine ⟨1255539624219658228122871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6696211329171510549988645 1255539624219658228122871)
          ·
            refine ⟨1883309436329487342184307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1255539624219658228122871 1883309436329487342184307)
            ·
              refine ⟨2824964154494231013276461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1883309436329487342184307 2824964154494231013276461)
              ·
                refine ⟨1059361557935336629978673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2824964154494231013276461 1059361557935336629978673)
                ·
                  refine ⟨794521168451502472484005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1059361557935336629978673 794521168451502472484005)
                  ·
                    refine ⟨148972719084656713590751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 794521168451502472484005 148972719084656713590751)
                    ·
                      rfl

theorem cell22_435185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 3, 2, 4].length) (baseStart_435185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_435185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_435185 prefixEnd_435185 := by exact prefixLift 435185
  have htrace : WordTrace (prefixWord ++ tailWord_435185) baseStart_435185 baseEnd_435185 := by
    simpa [prefixWord, tailWord_435185, baseEnd_435185] using wordTrace_append hprefix tailTrace_435185
  have hstable : (prefixWord ++ tailWord_435185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435185).length < 2 ^ (prefixWord ++ tailWord_435185).sum := by decide
  have hdescent : baseEnd_435185 < baseStart_435185 := by decide
  rcases family_descends (prefixWord ++ tailWord_435185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435243 : List Nat := [1, 1, 1, 1, 2, 1, 5, 2, 1, 7]
def baseStart_435243 : Nat := 118140960795 + 435243 * 2 ^ 59
def prefixEnd_435243 : Nat := 4983230072969 + 3 ^ 40 * 435243 * 2
def baseEnd_435243 : Nat := 148992573669963895640573

theorem tailTrace_435243 : CollatzResearch.WordTrace tailWord_435243 prefixEnd_435243 148992573669963895640573 := by
  unfold tailWord_435243
  simp only [CollatzResearch.WordTrace]
  refine ⟨15874616362196419431510383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10583077574797612954340255 15874616362196419431510383)
  ·
    refine ⟨23811924543294629147265575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15874616362196419431510383 23811924543294629147265575)
    ·
      refine ⟨35717886814941943720898363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23811924543294629147265575 35717886814941943720898363)
      ·
        refine ⟨53576830222412915581347545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35717886814941943720898363 53576830222412915581347545)
        ·
          refine ⟨40182622666809686686010659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53576830222412915581347545 40182622666809686686010659)
          ·
            refine ⟨60273934000214530029015989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40182622666809686686010659 60273934000214530029015989)
            ·
              refine ⟨5650681312520112190220249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60273934000214530029015989 5650681312520112190220249)
              ·
                refine ⟨4238010984390084142665187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5650681312520112190220249 4238010984390084142665187)
                ·
                  refine ⟨6357016476585126213997781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4238010984390084142665187 6357016476585126213997781)
                  ·
                    refine ⟨148992573669963895640573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6357016476585126213997781 148992573669963895640573)
                    ·
                      rfl

theorem cell22_435243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 7].length) (baseStart_435243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_435243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_435243 prefixEnd_435243 := by exact prefixLift 435243
  have htrace : WordTrace (prefixWord ++ tailWord_435243) baseStart_435243 baseEnd_435243 := by
    simpa [prefixWord, tailWord_435243, baseEnd_435243] using wordTrace_append hprefix tailTrace_435243
  have hstable : (prefixWord ++ tailWord_435243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435243).length < 2 ^ (prefixWord ++ tailWord_435243).sum := by decide
  have hdescent : baseEnd_435243 < baseStart_435243 := by decide
  rcases family_descends (prefixWord ++ tailWord_435243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435249 : List Nat := [1, 2, 2, 3, 1, 2, 4, 3, 1, 3]
def baseStart_435249 : Nat := 118140960795 + 435249 * 2 ^ 59
def prefixEnd_435249 : Nat := 4983230072969 + 3 ^ 40 * 435249 * 2
def baseEnd_435249 : Nat := 148994627592581879990555

theorem tailTrace_435249 : CollatzResearch.WordTrace tailWord_435249 prefixEnd_435249 148994627592581879990555 := by
  unfold tailWord_435249
  simp only [CollatzResearch.WordTrace]
  refine ⟨15874835200174682456228801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10583223466783121637485867 15874835200174682456228801)
  ·
    refine ⟨11906126400131011842171601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15874835200174682456228801 11906126400131011842171601)
    ·
      refine ⟨8929594800098258881628701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11906126400131011842171601 8929594800098258881628701)
      ·
        refine ⟨3348598050036847080610763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8929594800098258881628701 3348598050036847080610763)
        ·
          refine ⟨5022897075055270620916145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3348598050036847080610763 5022897075055270620916145)
          ·
            refine ⟨3767172806291452965687109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5022897075055270620916145 3767172806291452965687109)
            ·
              refine ⟨706344901179647431066333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3767172806291452965687109 706344901179647431066333)
              ·
                refine ⟨264879337942367786649875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 706344901179647431066333 264879337942367786649875)
                ·
                  refine ⟨397319006913551679974813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 264879337942367786649875 397319006913551679974813)
                  ·
                    refine ⟨148994627592581879990555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 397319006913551679974813 148994627592581879990555)
                    ·
                      rfl

theorem cell22_435249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 3, 1, 3].length) (baseStart_435249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_435249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_435249 prefixEnd_435249 := by exact prefixLift 435249
  have htrace : WordTrace (prefixWord ++ tailWord_435249) baseStart_435249 baseEnd_435249 := by
    simpa [prefixWord, tailWord_435249, baseEnd_435249] using wordTrace_append hprefix tailTrace_435249
  have hstable : (prefixWord ++ tailWord_435249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435249).length < 2 ^ (prefixWord ++ tailWord_435249).sum := by decide
  have hdescent : baseEnd_435249 < baseStart_435249 := by decide
  rcases family_descends (prefixWord ++ tailWord_435249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435260 : List Nat := [2, 2, 2, 2, 2, 2, 1, 2, 2, 5]
def baseStart_435260 : Nat := 118140960795 + 435260 * 2 ^ 59
def prefixEnd_435260 : Nat := 4983230072969 + 3 ^ 40 * 435260 * 2
def baseEnd_435260 : Nat := 148998393117381517965521

theorem tailTrace_435260 : CollatzResearch.WordTrace tailWord_435260 prefixEnd_435260 148998393117381517965521 := by
  unfold tailWord_435260
  simp only [CollatzResearch.WordTrace]
  refine ⟨7937618201567415667439617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10583490935423220889919489 7937618201567415667439617)
  ·
    refine ⟨5953213651175561750579713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7937618201567415667439617 5953213651175561750579713)
    ·
      refine ⟨4464910238381671312934785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5953213651175561750579713 4464910238381671312934785)
      ·
        refine ⟨3348682678786253484701089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4464910238381671312934785 3348682678786253484701089)
        ·
          refine ⟨2511512009089690113525817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3348682678786253484701089 2511512009089690113525817)
          ·
            refine ⟨1883634006817267585144363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2511512009089690113525817 1883634006817267585144363)
            ·
              refine ⟨2825451010225901377716545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1883634006817267585144363 2825451010225901377716545)
              ·
                refine ⟨2119088257669426033287409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2825451010225901377716545 2119088257669426033287409)
                ·
                  refine ⟨1589316193252069524965557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2119088257669426033287409 1589316193252069524965557)
                  ·
                    refine ⟨148998393117381517965521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1589316193252069524965557 148998393117381517965521)
                    ·
                      rfl

theorem cell22_435260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_435260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_435260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_435260 prefixEnd_435260 := by exact prefixLift 435260
  have htrace : WordTrace (prefixWord ++ tailWord_435260) baseStart_435260 baseEnd_435260 := by
    simpa [prefixWord, tailWord_435260, baseEnd_435260] using wordTrace_append hprefix tailTrace_435260
  have hstable : (prefixWord ++ tailWord_435260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435260).length < 2 ^ (prefixWord ++ tailWord_435260).sum := by decide
  have hdescent : baseEnd_435260 < baseStart_435260 := by decide
  rcases family_descends (prefixWord ++ tailWord_435260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435262 : List Nat := [4, 2, 1, 3, 1, 2, 1, 1, 7]
def baseStart_435262 : Nat := 118140960795 + 435262 * 2 ^ 59
def prefixEnd_435262 : Nat := 4983230072969 + 3 ^ 40 * 435262 * 2
def baseEnd_435262 : Nat := 49666359252751393138505

theorem tailTrace_435262 : CollatzResearch.WordTrace tailWord_435262 prefixEnd_435262 49666359252751393138505 := by
  unfold tailWord_435262
  simp only [CollatzResearch.WordTrace]
  refine ⟨1984413668640948209556505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10583539566085057117634693 1984413668640948209556505)
  ·
    refine ⟨1488310251480711157167379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1984413668640948209556505 1488310251480711157167379)
    ·
      refine ⟨2232465377221066735751069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1488310251480711157167379 2232465377221066735751069)
      ·
        refine ⟨837174516457900025906651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2232465377221066735751069 837174516457900025906651)
        ·
          refine ⟨1255761774686850038859977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 837174516457900025906651 1255761774686850038859977)
          ·
            refine ⟨941821331015137529144983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1255761774686850038859977 941821331015137529144983)
            ·
              refine ⟨1412731996522706293717475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 941821331015137529144983 1412731996522706293717475)
              ·
                refine ⟨2119097994784059440576213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1412731996522706293717475 2119097994784059440576213)
                ·
                  refine ⟨49666359252751393138505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2119097994784059440576213 49666359252751393138505)
                  ·
                    rfl

theorem cell22_435262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_435262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_435262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_435262 prefixEnd_435262 := by exact prefixLift 435262
  have htrace : WordTrace (prefixWord ++ tailWord_435262) baseStart_435262 baseEnd_435262 := by
    simpa [prefixWord, tailWord_435262, baseEnd_435262] using wordTrace_append hprefix tailTrace_435262
  have hstable : (prefixWord ++ tailWord_435262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435262).length < 2 ^ (prefixWord ++ tailWord_435262).sum := by decide
  have hdescent : baseEnd_435262 < baseStart_435262 := by decide
  rcases family_descends (prefixWord ++ tailWord_435262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435277 : List Nat := [1, 6, 1, 1, 1, 2, 2, 1, 2, 5]
def baseStart_435277 : Nat := 118140960795 + 435277 * 2 ^ 59
def prefixEnd_435277 : Nat := 4983230072969 + 3 ^ 40 * 435277 * 2
def baseEnd_435277 : Nat := 149004212564799140290469

theorem tailTrace_435277 : CollatzResearch.WordTrace tailWord_435277 prefixEnd_435277 149004212564799140290469 := by
  unfold tailWord_435277
  simp only [CollatzResearch.WordTrace]
  refine ⟨15875856444073243238248085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10583904296048828825498723 15875856444073243238248085)
  ·
    refine ⟨744180770815933276792879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15875856444073243238248085 744180770815933276792879)
    ·
      refine ⟨1116271156223899915189319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 744180770815933276792879 1116271156223899915189319)
      ·
        refine ⟨1674406734335849872783979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1116271156223899915189319 1674406734335849872783979)
        ·
          refine ⟨2511610101503774809175969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1674406734335849872783979 2511610101503774809175969)
          ·
            refine ⟨1883707576127831106881977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2511610101503774809175969 1883707576127831106881977)
            ·
              refine ⟨1412780682095873330161483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1883707576127831106881977 1412780682095873330161483)
              ·
                refine ⟨2119171023143809995242225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1412780682095873330161483 2119171023143809995242225)
                ·
                  refine ⟨1589378267357857496431669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2119171023143809995242225 1589378267357857496431669)
                  ·
                    refine ⟨149004212564799140290469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1589378267357857496431669 149004212564799140290469)
                    ·
                      rfl

theorem cell22_435277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_435277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_435277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_435277 prefixEnd_435277 := by exact prefixLift 435277
  have htrace : WordTrace (prefixWord ++ tailWord_435277) baseStart_435277 baseEnd_435277 := by
    simpa [prefixWord, tailWord_435277, baseEnd_435277] using wordTrace_append hprefix tailTrace_435277
  have hstable : (prefixWord ++ tailWord_435277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435277).length < 2 ^ (prefixWord ++ tailWord_435277).sum := by decide
  have hdescent : baseEnd_435277 < baseStart_435277 := by decide
  rcases family_descends (prefixWord ++ tailWord_435277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435320 : List Nat := [2, 1, 2, 1, 1, 1, 5, 1, 4, 4]
def baseStart_435320 : Nat := 118140960795 + 435320 * 2 ^ 59
def prefixEnd_435320 : Nat := 4983230072969 + 3 ^ 40 * 435320 * 2
def baseEnd_435320 : Nat := 149018932343561361465337

theorem tailTrace_435320 : CollatzResearch.WordTrace tailWord_435320 prefixEnd_435320 149018932343561361465337 := by
  unfold tailWord_435320
  simp only [CollatzResearch.WordTrace]
  refine ⟨7938712391458730791031707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10584949855278307721375609 7938712391458730791031707)
  ·
    refine ⟨11908068587188096186547561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7938712391458730791031707 11908068587188096186547561)
    ·
      refine ⟨8931051440391072139910671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11908068587188096186547561 8931051440391072139910671)
      ·
        refine ⟨13396577160586608209866007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8931051440391072139910671 13396577160586608209866007)
        ·
          refine ⟨20094865740879912314799011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13396577160586608209866007 20094865740879912314799011)
          ·
            refine ⟨30142298611319868472198517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20094865740879912314799011 30142298611319868472198517)
            ·
              refine ⟨2825840494811237669268611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30142298611319868472198517 2825840494811237669268611)
              ·
                refine ⟨4238760742216856503902917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2825840494811237669268611 4238760742216856503902917)
                ·
                  refine ⟨794767639165660594481797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4238760742216856503902917 794767639165660594481797)
                  ·
                    refine ⟨149018932343561361465337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 794767639165660594481797 149018932343561361465337)
                    ·
                      rfl

theorem cell22_435320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 4, 4].length) (baseStart_435320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_435320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_435320 prefixEnd_435320 := by exact prefixLift 435320
  have htrace : WordTrace (prefixWord ++ tailWord_435320) baseStart_435320 baseEnd_435320 := by
    simpa [prefixWord, tailWord_435320, baseEnd_435320] using wordTrace_append hprefix tailTrace_435320
  have hstable : (prefixWord ++ tailWord_435320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435320).length < 2 ^ (prefixWord ++ tailWord_435320).sum := by decide
  have hdescent : baseEnd_435320 < baseStart_435320 := by decide
  rcases family_descends (prefixWord ++ tailWord_435320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435324 : List Nat := [2, 2, 2, 1, 1, 3, 5, 2, 4]
def baseStart_435324 : Nat := 118140960795 + 435324 * 2 ^ 59
def prefixEnd_435324 : Nat := 4983230072969 + 3 ^ 40 * 435324 * 2
def baseEnd_435324 : Nat := 49673433875102228121775

theorem tailTrace_435324 : CollatzResearch.WordTrace tailWord_435324 prefixEnd_435324 49673433875102228121775 := by
  unfold tailWord_435324
  simp only [CollatzResearch.WordTrace]
  refine ⟨7938785337451485132604513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10585047116601980176806017 7938785337451485132604513)
  ·
    refine ⟨5954089003088613849453385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7938785337451485132604513 5954089003088613849453385)
    ·
      refine ⟨4465566752316460387090039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5954089003088613849453385 4465566752316460387090039)
      ·
        refine ⟨6698350128474690580635059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4465566752316460387090039 6698350128474690580635059)
        ·
          refine ⟨10047525192712035870952589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6698350128474690580635059 10047525192712035870952589)
          ·
            refine ⟨3767821947267013451607221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10047525192712035870952589 3767821947267013451607221)
            ·
              refine ⟨353233307556282511088177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3767821947267013451607221 353233307556282511088177)
              ·
                refine ⟨264924980667211883316133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 353233307556282511088177 264924980667211883316133)
                ·
                  refine ⟨49673433875102228121775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 264924980667211883316133 49673433875102228121775)
                  ·
                    rfl

theorem cell22_435324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5, 2, 4].length) (baseStart_435324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_435324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_435324 prefixEnd_435324 := by exact prefixLift 435324
  have htrace : WordTrace (prefixWord ++ tailWord_435324) baseStart_435324 baseEnd_435324 := by
    simpa [prefixWord, tailWord_435324, baseEnd_435324] using wordTrace_append hprefix tailTrace_435324
  have hstable : (prefixWord ++ tailWord_435324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435324).length < 2 ^ (prefixWord ++ tailWord_435324).sum := by decide
  have hdescent : baseEnd_435324 < baseStart_435324 := by decide
  rcases family_descends (prefixWord ++ tailWord_435324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435354 : List Nat := [3, 1, 1, 5, 1, 2, 2, 1, 2, 4]
def baseStart_435354 : Nat := 118140960795 + 435354 * 2 ^ 59
def prefixEnd_435354 : Nat := 4983230072969 + 3 ^ 40 * 435354 * 2
def baseEnd_435354 : Nat := 149030571238396606115233

theorem tailTrace_435354 : CollatzResearch.WordTrace tailWord_435354 prefixEnd_435354 149030571238396606115233 := by
  unfold tailWord_435354
  simp only [CollatzResearch.WordTrace]
  refine ⟨3969666216198571347200279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10585776576529523592534077 3969666216198571347200279)
  ·
    refine ⟨5954499324297857020800419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3969666216198571347200279 5954499324297857020800419)
    ·
      refine ⟨8931748986446785531200629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5954499324297857020800419 8931748986446785531200629)
      ·
        refine ⟨837351467479386143550059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8931748986446785531200629 837351467479386143550059)
        ·
          refine ⟨1256027201219079215325089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 837351467479386143550059 1256027201219079215325089)
          ·
            refine ⟨942020400914309411493817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1256027201219079215325089 942020400914309411493817)
            ·
              refine ⟨706515300685732058620363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 942020400914309411493817 706515300685732058620363)
              ·
                refine ⟨1059772951028598087930545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 706515300685732058620363 1059772951028598087930545)
                ·
                  refine ⟨794829713271448565947909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1059772951028598087930545 794829713271448565947909)
                  ·
                    refine ⟨149030571238396606115233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 794829713271448565947909 149030571238396606115233)
                    ·
                      rfl

theorem cell22_435354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 1, 2, 4].length) (baseStart_435354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_435354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_435354 prefixEnd_435354 := by exact prefixLift 435354
  have htrace : WordTrace (prefixWord ++ tailWord_435354) baseStart_435354 baseEnd_435354 := by
    simpa [prefixWord, tailWord_435354, baseEnd_435354] using wordTrace_append hprefix tailTrace_435354
  have hstable : (prefixWord ++ tailWord_435354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435354).length < 2 ^ (prefixWord ++ tailWord_435354).sum := by decide
  have hdescent : baseEnd_435354 < baseStart_435354 := by decide
  rcases family_descends (prefixWord ++ tailWord_435354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435405 : List Nat := [1, 6, 2, 2, 2, 1, 1, 1, 2, 4]
def baseStart_435405 : Nat := 118140960795 + 435405 * 2 ^ 59
def prefixEnd_435405 : Nat := 4983230072969 + 3 ^ 40 * 435405 * 2
def baseEnd_435405 : Nat := 149048029580649473090077

theorem tailTrace_435405 : CollatzResearch.WordTrace tailWord_435405 prefixEnd_435405 149048029580649473090077 := by
  unfold tailWord_435405
  simp only [CollatzResearch.WordTrace]
  refine ⟨15880524987609521098907669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10587016658406347399271779 15880524987609521098907669)
  ·
    refine ⟨744399608794196301511297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15880524987609521098907669 744399608794196301511297)
    ·
      refine ⟨558299706595647226133473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 744399608794196301511297 558299706595647226133473)
      ·
        refine ⟨418724779946735419600105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 558299706595647226133473 418724779946735419600105)
        ·
          refine ⟨314043584960051564700079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 418724779946735419600105 314043584960051564700079)
          ·
            refine ⟨471065377440077347050119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314043584960051564700079 471065377440077347050119)
            ·
              refine ⟨706598066160116020575179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 471065377440077347050119 706598066160116020575179)
              ·
                refine ⟨1059897099240174030862769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 706598066160116020575179 1059897099240174030862769)
                ·
                  refine ⟨794922824430130523147077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1059897099240174030862769 794922824430130523147077)
                  ·
                    refine ⟨149048029580649473090077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 794922824430130523147077 149048029580649473090077)
                    ·
                      rfl

theorem cell22_435405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_435405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_435405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_435405 prefixEnd_435405 := by exact prefixLift 435405
  have htrace : WordTrace (prefixWord ++ tailWord_435405) baseStart_435405 baseEnd_435405 := by
    simpa [prefixWord, tailWord_435405, baseEnd_435405] using wordTrace_append hprefix tailTrace_435405
  have hstable : (prefixWord ++ tailWord_435405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435405).length < 2 ^ (prefixWord ++ tailWord_435405).sum := by decide
  have hdescent : baseEnd_435405 < baseStart_435405 := by decide
  rcases family_descends (prefixWord ++ tailWord_435405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435431 : List Nat := [1, 1, 5, 3, 2, 2, 1, 2, 5]
def baseStart_435431 : Nat := 118140960795 + 435431 * 2 ^ 59
def prefixEnd_435431 : Nat := 4983230072969 + 3 ^ 40 * 435431 * 2
def baseEnd_435431 : Nat := 49685643303998023979999

theorem tailTrace_435431 : CollatzResearch.WordTrace tailWord_435431 prefixEnd_435431 49685643303998023979999 := by
  unfold tailWord_435431
  simp only [CollatzResearch.WordTrace]
  refine ⟨15881473285515327539354147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10587648857010218359569431 15881473285515327539354147)
  ·
    refine ⟨23822209928272991309031221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15881473285515327539354147 23822209928272991309031221)
    ·
      refine ⟨2233332180775592935221677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23822209928272991309031221 2233332180775592935221677)
      ·
        refine ⟨837499567790847350708129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2233332180775592935221677 837499567790847350708129)
        ·
          refine ⟨628124675843135513031097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 837499567790847350708129 628124675843135513031097)
          ·
            refine ⟨471093506882351634773323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 628124675843135513031097 471093506882351634773323)
            ·
              refine ⟨706640260323527452159985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 471093506882351634773323 706640260323527452159985)
              ·
                refine ⟨529980195242645589119989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 706640260323527452159985 529980195242645589119989)
                ·
                  refine ⟨49685643303998023979999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 529980195242645589119989 49685643303998023979999)
                  ·
                    rfl

theorem cell22_435431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 2, 5].length) (baseStart_435431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_435431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_435431 prefixEnd_435431 := by exact prefixLift 435431
  have htrace : WordTrace (prefixWord ++ tailWord_435431) baseStart_435431 baseEnd_435431 := by
    simpa [prefixWord, tailWord_435431, baseEnd_435431] using wordTrace_append hprefix tailTrace_435431
  have hstable : (prefixWord ++ tailWord_435431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435431).length < 2 ^ (prefixWord ++ tailWord_435431).sum := by decide
  have hdescent : baseEnd_435431 < baseStart_435431 := by decide
  rcases family_descends (prefixWord ++ tailWord_435431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435440 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 2, 9]
def baseStart_435440 : Nat := 118140960795 + 435440 * 2 ^ 59
def prefixEnd_435440 : Nat := 4983230072969 + 3 ^ 40 * 435440 * 2
def baseEnd_435440 : Nat := 149060010795921048464969

theorem tailTrace_435440 : CollatzResearch.WordTrace tailWord_435440 prefixEnd_435440 149060010795921048464969 := by
  unfold tailWord_435440
  simp only [CollatzResearch.WordTrace]
  refine ⟨7940900771241361038215887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10587867694988481384287849 7940900771241361038215887)
  ·
    refine ⟨11911351156862041557323831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7940900771241361038215887 11911351156862041557323831)
    ·
      refine ⟨17867026735293062335985747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11911351156862041557323831 17867026735293062335985747)
      ·
        refine ⟨26800540102939593503978621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17867026735293062335985747 26800540102939593503978621)
        ·
          refine ⟨10050202538602347563991983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26800540102939593503978621 10050202538602347563991983)
          ·
            refine ⟨15075303807903521345987975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10050202538602347563991983 15075303807903521345987975)
            ·
              refine ⟨22612955711855282018981963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15075303807903521345987975 22612955711855282018981963)
              ·
                refine ⟨33919433567782923028472945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22612955711855282018981963 33919433567782923028472945)
                ·
                  refine ⟨25439575175837192271354709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33919433567782923028472945 25439575175837192271354709)
                  ·
                    refine ⟨149060010795921048464969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 25439575175837192271354709 149060010795921048464969)
                    ·
                      rfl

theorem cell22_435440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 2, 9].length) (baseStart_435440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_435440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_435440 prefixEnd_435440 := by exact prefixLift 435440
  have htrace : WordTrace (prefixWord ++ tailWord_435440) baseStart_435440 baseEnd_435440 := by
    simpa [prefixWord, tailWord_435440, baseEnd_435440] using wordTrace_append hprefix tailTrace_435440
  have hstable : (prefixWord ++ tailWord_435440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435440).length < 2 ^ (prefixWord ++ tailWord_435440).sum := by decide
  have hdescent : baseEnd_435440 < baseStart_435440 := by decide
  rcases family_descends (prefixWord ++ tailWord_435440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435536 : List Nat := [2, 1, 1, 1, 1, 5, 2, 5, 1, 3]
def baseStart_435536 : Nat := 118140960795 + 435536 * 2 ^ 59
def prefixEnd_435536 : Nat := 4983230072969 + 3 ^ 40 * 435536 * 2
def baseEnd_435536 : Nat := 149092873557808798064675

theorem tailTrace_435536 : CollatzResearch.WordTrace tailWord_435536 prefixEnd_435536 149092873557808798064675 := by
  unfold tailWord_435536
  simp only [CollatzResearch.WordTrace]
  refine ⟨7942651475067465235963231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10590201966756620314617641 7942651475067465235963231)
  ·
    refine ⟨11913977212601197853944847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7942651475067465235963231 11913977212601197853944847)
    ·
      refine ⟨17870965818901796780917271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11913977212601197853944847 17870965818901796780917271)
      ·
        refine ⟨26806448728352695171375907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17870965818901796780917271 26806448728352695171375907)
        ·
          refine ⟨40209673092529042757063861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26806448728352695171375907 40209673092529042757063861)
          ·
            refine ⟨3769656852424597758474737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40209673092529042757063861 3769656852424597758474737)
            ·
              refine ⟨2827242639318448318856053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3769656852424597758474737 2827242639318448318856053)
              ·
                refine ⟨265053997436104529892755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2827242639318448318856053 265053997436104529892755)
                ·
                  refine ⟨397580996154156794839133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 265053997436104529892755 397580996154156794839133)
                  ·
                    refine ⟨149092873557808798064675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 397580996154156794839133 149092873557808798064675)
                    ·
                      rfl

theorem cell22_435536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 5, 1, 3].length) (baseStart_435536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_435536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_435536 prefixEnd_435536 := by exact prefixLift 435536
  have htrace : WordTrace (prefixWord ++ tailWord_435536) baseStart_435536 baseEnd_435536 := by
    simpa [prefixWord, tailWord_435536, baseEnd_435536] using wordTrace_append hprefix tailTrace_435536
  have hstable : (prefixWord ++ tailWord_435536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435536).length < 2 ^ (prefixWord ++ tailWord_435536).sum := by decide
  have hdescent : baseEnd_435536 < baseStart_435536 := by decide
  rcases family_descends (prefixWord ++ tailWord_435536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435564 : List Nat := [2, 2, 1, 1, 5, 2, 1, 1, 2, 5]
def baseStart_435564 : Nat := 118140960795 + 435564 * 2 ^ 59
def prefixEnd_435564 : Nat := 4983230072969 + 3 ^ 40 * 435564 * 2
def baseEnd_435564 : Nat := 149102458530026058364589

theorem tailTrace_435564 : CollatzResearch.WordTrace tailWord_435564 prefixEnd_435564 149102458530026058364589 := by
  unfold tailWord_435564
  simp only [CollatzResearch.WordTrace]
  refine ⟨7943162097016745626972873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10590882796022327502630497 7943162097016745626972873)
  ·
    refine ⟨5957371572762559220229655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7943162097016745626972873 5957371572762559220229655)
    ·
      refine ⟨8936057359143838830344483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5957371572762559220229655 8936057359143838830344483)
      ·
        refine ⟨13404086038715758245516725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8936057359143838830344483 13404086038715758245516725)
        ·
          refine ⟨1256633066129602335517193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13404086038715758245516725 1256633066129602335517193)
          ·
            refine ⟨942474799597201751637895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1256633066129602335517193 942474799597201751637895)
            ·
              refine ⟨1413712199395802627456843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 942474799597201751637895 1413712199395802627456843)
              ·
                refine ⟨2120568299093703941185265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1413712199395802627456843 2120568299093703941185265)
                ·
                  refine ⟨1590426224320277955888949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2120568299093703941185265 1590426224320277955888949)
                  ·
                    refine ⟨149102458530026058364589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1590426224320277955888949 149102458530026058364589)
                    ·
                      rfl

theorem cell22_435564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 5].length) (baseStart_435564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_435564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_435564 prefixEnd_435564 := by exact prefixLift 435564
  have htrace : WordTrace (prefixWord ++ tailWord_435564) baseStart_435564 baseEnd_435564 := by
    simpa [prefixWord, tailWord_435564, baseEnd_435564] using wordTrace_append hprefix tailTrace_435564
  have hstable : (prefixWord ++ tailWord_435564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435564).length < 2 ^ (prefixWord ++ tailWord_435564).sum := by decide
  have hdescent : baseEnd_435564 < baseStart_435564 := by decide
  rcases family_descends (prefixWord ++ tailWord_435564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435577 : List Nat := [1, 2, 1, 3, 2, 1, 3, 1, 8]
def baseStart_435577 : Nat := 118140960795 + 435577 * 2 ^ 59
def prefixEnd_435577 : Nat := 4983230072969 + 3 ^ 40 * 435577 * 2
def baseEnd_435577 : Nat := 49702302898566119263183

theorem tailTrace_435577 : CollatzResearch.WordTrace tailWord_435577 prefixEnd_435577 49702302898566119263183 := by
  unfold tailWord_435577
  simp only [CollatzResearch.WordTrace]
  refine ⟨15886798342986394474168985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10591198895324262982779323 15886798342986394474168985)
  ·
    refine ⟨11915098757239795855626739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15886798342986394474168985 11915098757239795855626739)
    ·
      refine ⟨17872648135859693783440109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11915098757239795855626739 17872648135859693783440109)
      ·
        refine ⟨6702243050947385168790041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17872648135859693783440109 6702243050947385168790041)
        ·
          refine ⟨5026682288210538876592531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6702243050947385168790041 5026682288210538876592531)
          ·
            refine ⟨7540023432315808314888797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5026682288210538876592531 7540023432315808314888797)
            ·
              refine ⟨2827508787118428118083299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7540023432315808314888797 2827508787118428118083299)
              ·
                refine ⟨4241263180677642177124949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2827508787118428118083299 4241263180677642177124949)
                ·
                  refine ⟨49702302898566119263183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4241263180677642177124949 49702302898566119263183)
                  ·
                    rfl

theorem cell22_435577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 8].length) (baseStart_435577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_435577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_435577 prefixEnd_435577 := by exact prefixLift 435577
  have htrace : WordTrace (prefixWord ++ tailWord_435577) baseStart_435577 baseEnd_435577 := by
    simpa [prefixWord, tailWord_435577, baseEnd_435577] using wordTrace_append hprefix tailTrace_435577
  have hstable : (prefixWord ++ tailWord_435577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435577).length < 2 ^ (prefixWord ++ tailWord_435577).sum := by decide
  have hdescent : baseEnd_435577 < baseStart_435577 := by decide
  rcases family_descends (prefixWord ++ tailWord_435577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435579 : List Nat := [1, 1, 1, 1, 1, 6, 2, 4, 1, 4]
def baseStart_435579 : Nat := 118140960795 + 435579 * 2 ^ 59
def prefixEnd_435579 : Nat := 4983230072969 + 3 ^ 40 * 435579 * 2
def baseEnd_435579 : Nat := 149107593336571019239543

theorem tailTrace_435579 : CollatzResearch.WordTrace tailWord_435579 prefixEnd_435579 149107593336571019239543 := by
  unfold tailWord_435579
  simp only [CollatzResearch.WordTrace]
  refine ⟨15886871288979148815741791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10591247525986099210494527 15886871288979148815741791)
  ·
    refine ⟨23830306933468723223612687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15886871288979148815741791 23830306933468723223612687)
    ·
      refine ⟨35745460400203084835419031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23830306933468723223612687 35745460400203084835419031)
      ·
        refine ⟨53618190600304627253128547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35745460400203084835419031 53618190600304627253128547)
        ·
          refine ⟨80427285900456940879692821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53618190600304627253128547 80427285900456940879692821)
          ·
            refine ⟨3770029026583919103735601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 80427285900456940879692821 3770029026583919103735601)
            ·
              refine ⟨2827521769937939327801701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3770029026583919103735601 2827521769937939327801701)
              ·
                refine ⟨530160331863363623962819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2827521769937939327801701 530160331863363623962819)
                ·
                  refine ⟨795240497795045435944229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 530160331863363623962819 795240497795045435944229)
                  ·
                    refine ⟨149107593336571019239543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 795240497795045435944229 149107593336571019239543)
                    ·
                      rfl

theorem cell22_435579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 4, 1, 4].length) (baseStart_435579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_435579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_435579 prefixEnd_435579 := by exact prefixLift 435579
  have htrace : WordTrace (prefixWord ++ tailWord_435579) baseStart_435579 baseEnd_435579 := by
    simpa [prefixWord, tailWord_435579, baseEnd_435579] using wordTrace_append hprefix tailTrace_435579
  have hstable : (prefixWord ++ tailWord_435579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435579).length < 2 ^ (prefixWord ++ tailWord_435579).sum := by decide
  have hdescent : baseEnd_435579 < baseStart_435579 := by decide
  rcases family_descends (prefixWord ++ tailWord_435579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435669 : List Nat := [1, 3, 2, 3, 1, 1, 2, 1, 2, 6]
def baseStart_435669 : Nat := 118140960795 + 435669 * 2 ^ 59
def prefixEnd_435669 : Nat := 4983230072969 + 3 ^ 40 * 435669 * 2
def baseEnd_435669 : Nat := 149138402175840784489267

theorem tailTrace_435669 : CollatzResearch.WordTrace tailWord_435669 prefixEnd_435669 149138402175840784489267 := by
  unfold tailWord_435669
  simp only [CollatzResearch.WordTrace]
  refine ⟨15890153858653094186518061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10593435905768729457678707 15890153858653094186518061)
  ·
    refine ⟨5958807696994910319944273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15890153858653094186518061 5958807696994910319944273)
    ·
      refine ⟨4469105772746182739958205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5958807696994910319944273 4469105772746182739958205)
      ·
        refine ⟨1675914664779818527484327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4469105772746182739958205 1675914664779818527484327)
        ·
          refine ⟨2513871997169727791226491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1675914664779818527484327 2513871997169727791226491)
          ·
            refine ⟨3770807995754591686839737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2513871997169727791226491 3770807995754591686839737)
            ·
              refine ⟨2828105996815943765129803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3770807995754591686839737 2828105996815943765129803)
              ·
                refine ⟨4242158995223915647694705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2828105996815943765129803 4242158995223915647694705)
                ·
                  refine ⟨3181619246417936735771029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4242158995223915647694705 3181619246417936735771029)
                  ·
                    refine ⟨149138402175840784489267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3181619246417936735771029 149138402175840784489267)
                    ·
                      rfl

theorem cell22_435669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_435669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_435669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_435669 prefixEnd_435669 := by exact prefixLift 435669
  have htrace : WordTrace (prefixWord ++ tailWord_435669) baseStart_435669 baseEnd_435669 := by
    simpa [prefixWord, tailWord_435669, baseEnd_435669] using wordTrace_append hprefix tailTrace_435669
  have hstable : (prefixWord ++ tailWord_435669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435669).length < 2 ^ (prefixWord ++ tailWord_435669).sum := by decide
  have hdescent : baseEnd_435669 < baseStart_435669 := by decide
  rcases family_descends (prefixWord ++ tailWord_435669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435722 : List Nat := [3, 1, 2, 2, 2, 4, 2, 2, 1, 3]
def baseStart_435722 : Nat := 118140960795 + 435722 * 2 ^ 59
def prefixEnd_435722 : Nat := 4983230072969 + 3 ^ 40 * 435722 * 2
def baseEnd_435722 : Nat := 149156545158966312914105

theorem tailTrace_435722 : CollatzResearch.WordTrace tailWord_435722 prefixEnd_435722 149156545158966312914105 := by
  unfold tailWord_435722
  simp only [CollatzResearch.WordTrace]
  refine ⟨3973021731865271059549355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10594724618307389492131613 3973021731865271059549355)
  ·
    refine ⟨5959532597797906589324033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3973021731865271059549355 5959532597797906589324033)
    ·
      refine ⟨4469649448348429941993025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5959532597797906589324033 4469649448348429941993025)
      ·
        refine ⟨3352237086261322456494769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4469649448348429941993025 3352237086261322456494769)
        ·
          refine ⟨2514177814695991842371077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3352237086261322456494769 2514177814695991842371077)
          ·
            refine ⟨471408340255498470444577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2514177814695991842371077 471408340255498470444577)
            ·
              refine ⟨353556255191623852833433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 471408340255498470444577 353556255191623852833433)
              ·
                refine ⟨265167191393717889625075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 353556255191623852833433 265167191393717889625075)
                ·
                  refine ⟨397750787090576834437613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 265167191393717889625075 397750787090576834437613)
                  ·
                    refine ⟨149156545158966312914105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 397750787090576834437613 149156545158966312914105)
                    ·
                      rfl

theorem cell22_435722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2, 2, 1, 3].length) (baseStart_435722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_435722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_435722 prefixEnd_435722 := by exact prefixLift 435722
  have htrace : WordTrace (prefixWord ++ tailWord_435722) baseStart_435722 baseEnd_435722 := by
    simpa [prefixWord, tailWord_435722, baseEnd_435722] using wordTrace_append hprefix tailTrace_435722
  have hstable : (prefixWord ++ tailWord_435722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435722).length < 2 ^ (prefixWord ++ tailWord_435722).sum := by decide
  have hdescent : baseEnd_435722 < baseStart_435722 := by decide
  rcases family_descends (prefixWord ++ tailWord_435722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435729 : List Nat := [1, 2, 2, 1, 1, 2, 4, 3, 6]
def baseStart_435729 : Nat := 118140960795 + 435729 * 2 ^ 59
def prefixEnd_435729 : Nat := 4983230072969 + 3 ^ 40 * 435729 * 2
def baseEnd_435729 : Nat := 49719647134006875996361

theorem tailTrace_435729 : CollatzResearch.WordTrace tailWord_435729 prefixEnd_435729 49719647134006875996361 := by
  unfold tailWord_435729
  simp only [CollatzResearch.WordTrace]
  refine ⟨15892342238435724433702241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10594894825623816289134827 15892342238435724433702241)
  ·
    refine ⟨11919256678826793325276681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15892342238435724433702241 11919256678826793325276681)
    ·
      refine ⟨8939442509120094993957511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11919256678826793325276681 8939442509120094993957511)
      ·
        refine ⟨13409163763680142490936267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8939442509120094993957511 13409163763680142490936267)
        ·
          refine ⟨20113745645520213736404401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13409163763680142490936267 20113745645520213736404401)
          ·
            refine ⟨15085309234140160302303301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20113745645520213736404401 15085309234140160302303301)
            ·
              refine ⟨2828495481401280056681869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15085309234140160302303301 2828495481401280056681869)
              ·
                refine ⟨1060685805525480021255701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2828495481401280056681869 1060685805525480021255701)
                ·
                  refine ⟨49719647134006875996361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1060685805525480021255701 49719647134006875996361)
                  ·
                    rfl

theorem cell22_435729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3, 6].length) (baseStart_435729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_435729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_435729 prefixEnd_435729 := by exact prefixLift 435729
  have htrace : WordTrace (prefixWord ++ tailWord_435729) baseStart_435729 baseEnd_435729 := by
    simpa [prefixWord, tailWord_435729, baseEnd_435729] using wordTrace_append hprefix tailTrace_435729
  have hstable : (prefixWord ++ tailWord_435729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435729).length < 2 ^ (prefixWord ++ tailWord_435729).sum := by decide
  have hdescent : baseEnd_435729 < baseStart_435729 := by decide
  rcases family_descends (prefixWord ++ tailWord_435729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435761 : List Nat := [1, 2, 2, 3, 1, 1, 1, 4, 4, 3]
def baseStart_435761 : Nat := 118140960795 + 435761 * 2 ^ 59
def prefixEnd_435761 : Nat := 4983230072969 + 3 ^ 40 * 435761 * 2
def baseEnd_435761 : Nat := 149169895655983211188985

theorem tailTrace_435761 : CollatzResearch.WordTrace tailWord_435761 prefixEnd_435761 149169895655983211188985 := by
  unfold tailWord_435761
  simp only [CollatzResearch.WordTrace]
  refine ⟨15893509374319793898867137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10595672916213195932578091 15893509374319793898867137)
  ·
    refine ⟨11920132030739845424150353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15893509374319793898867137 11920132030739845424150353)
    ·
      refine ⟨8940099023054884068112765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11920132030739845424150353 8940099023054884068112765)
      ·
        refine ⟨3352537133645581525542287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8940099023054884068112765 3352537133645581525542287)
        ·
          refine ⟨5028805700468372288313431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3352537133645581525542287 5028805700468372288313431)
          ·
            refine ⟨7543208550702558432470147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5028805700468372288313431 7543208550702558432470147)
            ·
              refine ⟨11314812826053837648705221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7543208550702558432470147 11314812826053837648705221)
              ·
                refine ⟨2121527404885094559132229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11314812826053837648705221 2121527404885094559132229)
                ·
                  refine ⟨397786388415955229837293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2121527404885094559132229 397786388415955229837293)
                  ·
                    refine ⟨149169895655983211188985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 397786388415955229837293 149169895655983211188985)
                    ·
                      rfl

theorem cell22_435761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 4, 3].length) (baseStart_435761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_435761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_435761 prefixEnd_435761 := by exact prefixLift 435761
  have htrace : WordTrace (prefixWord ++ tailWord_435761) baseStart_435761 baseEnd_435761 := by
    simpa [prefixWord, tailWord_435761, baseEnd_435761] using wordTrace_append hprefix tailTrace_435761
  have hstable : (prefixWord ++ tailWord_435761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435761).length < 2 ^ (prefixWord ++ tailWord_435761).sum := by decide
  have hdescent : baseEnd_435761 < baseStart_435761 := by decide
  rcases family_descends (prefixWord ++ tailWord_435761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435763 : List Nat := [1, 1, 1, 2, 4, 4, 2, 3, 4]
def baseStart_435763 : Nat := 118140960795 + 435763 * 2 ^ 59
def prefixEnd_435763 : Nat := 4983230072969 + 3 ^ 40 * 435763 * 2
def baseEnd_435763 : Nat := 49723526765618624212993

theorem tailTrace_435763 : CollatzResearch.WordTrace tailWord_435763 prefixEnd_435763 49723526765618624212993 := by
  unfold tailWord_435763
  simp only [CollatzResearch.WordTrace]
  refine ⟨15893582320312548240439943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10595721546875032160293295 15893582320312548240439943)
  ·
    refine ⟨23840373480468822360659915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15893582320312548240439943 23840373480468822360659915)
    ·
      refine ⟨35760560220703233540989873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23840373480468822360659915 35760560220703233540989873)
      ·
        refine ⟨26820420165527425155742405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35760560220703233540989873 26820420165527425155742405)
        ·
          refine ⟨5028828781036392216701701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26820420165527425155742405 5028828781036392216701701)
          ·
            refine ⟨942905396444323540631569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5028828781036392216701701 942905396444323540631569)
            ·
              refine ⟨707179047333242655473677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 942905396444323540631569 707179047333242655473677)
              ·
                refine ⟨265192142749965995802629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 707179047333242655473677 265192142749965995802629)
                ·
                  refine ⟨49723526765618624212993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 265192142749965995802629 49723526765618624212993)
                  ·
                    rfl

theorem cell22_435763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 3, 4].length) (baseStart_435763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_435763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_435763 prefixEnd_435763 := by exact prefixLift 435763
  have htrace : WordTrace (prefixWord ++ tailWord_435763) baseStart_435763 baseEnd_435763 := by
    simpa [prefixWord, tailWord_435763, baseEnd_435763] using wordTrace_append hprefix tailTrace_435763
  have hstable : (prefixWord ++ tailWord_435763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435763).length < 2 ^ (prefixWord ++ tailWord_435763).sum := by decide
  have hdescent : baseEnd_435763 < baseStart_435763 := by decide
  rcases family_descends (prefixWord ++ tailWord_435763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435765 : List Nat := [1, 3, 3, 1, 1, 5, 2, 1, 1, 4]
def baseStart_435765 : Nat := 118140960795 + 435765 * 2 ^ 59
def prefixEnd_435765 : Nat := 4983230072969 + 3 ^ 40 * 435765 * 2
def baseEnd_435765 : Nat := 149171264937728534088973

theorem tailTrace_435765 : CollatzResearch.WordTrace tailWord_435765 prefixEnd_435765 149171264937728534088973 := by
  unfold tailWord_435765
  simp only [CollatzResearch.WordTrace]
  refine ⟨15893655266305302582012749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10595770177536868388008499 15893655266305302582012749)
  ·
    refine ⟨5960120724864488468254781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15893655266305302582012749 5960120724864488468254781)
    ·
      refine ⟨2235045271824183175595543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5960120724864488468254781 2235045271824183175595543)
      ·
        refine ⟨3352567907736274763393315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2235045271824183175595543 3352567907736274763393315)
        ·
          refine ⟨5028851861604412145089973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3352567907736274763393315 5028851861604412145089973)
          ·
            refine ⟨471454862025413638602185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5028851861604412145089973 471454862025413638602185)
            ·
              refine ⟨353591146519060228951639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 471454862025413638602185 353591146519060228951639)
              ·
                refine ⟨530386719778590343427459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 353591146519060228951639 530386719778590343427459)
                ·
                  refine ⟨795580079667885515141189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 530386719778590343427459 795580079667885515141189)
                  ·
                    refine ⟨149171264937728534088973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 795580079667885515141189 149171264937728534088973)
                    ·
                      rfl

theorem cell22_435765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2, 1, 1, 4].length) (baseStart_435765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_435765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_435765 prefixEnd_435765 := by exact prefixLift 435765
  have htrace : WordTrace (prefixWord ++ tailWord_435765) baseStart_435765 baseEnd_435765 := by
    simpa [prefixWord, tailWord_435765, baseEnd_435765] using wordTrace_append hprefix tailTrace_435765
  have hstable : (prefixWord ++ tailWord_435765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435765).length < 2 ^ (prefixWord ++ tailWord_435765).sum := by decide
  have hdescent : baseEnd_435765 < baseStart_435765 := by decide
  rcases family_descends (prefixWord ++ tailWord_435765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435836 : List Nat := [2, 2, 2, 1, 1, 2, 1, 6, 5]
def baseStart_435836 : Nat := 118140960795 + 435836 * 2 ^ 59
def prefixEnd_435836 : Nat := 4983230072969 + 3 ^ 40 * 435836 * 2
def baseEnd_435836 : Nat := 49731856562902671854585

theorem tailTrace_435836 : CollatzResearch.WordTrace tailWord_435836 prefixEnd_435836 49731856562902671854585 := by
  unfold tailWord_435836
  simp only [CollatzResearch.WordTrace]
  refine ⟨7948122424524040853923681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10597496566032054471898241 7948122424524040853923681)
  ·
    refine ⟨5961091818393030640442761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7948122424524040853923681 5961091818393030640442761)
    ·
      refine ⟨4470818863794772980332071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5961091818393030640442761 4470818863794772980332071)
      ·
        refine ⟨6706228295692159470498107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4470818863794772980332071 6706228295692159470498107)
        ·
          refine ⟨10059342443538239205747161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6706228295692159470498107 10059342443538239205747161)
          ·
            refine ⟨7544506832653679404310371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10059342443538239205747161 7544506832653679404310371)
            ·
              refine ⟨11316760248980519106465557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7544506832653679404310371 11316760248980519106465557)
              ·
                refine ⟨530473136670961833115573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11316760248980519106465557 530473136670961833115573)
                ·
                  refine ⟨49731856562902671854585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 530473136670961833115573 49731856562902671854585)
                  ·
                    rfl

theorem cell22_435836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 6, 5].length) (baseStart_435836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_435836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_435836 prefixEnd_435836 := by exact prefixLift 435836
  have htrace : WordTrace (prefixWord ++ tailWord_435836) baseStart_435836 baseEnd_435836 := by
    simpa [prefixWord, tailWord_435836, baseEnd_435836] using wordTrace_append hprefix tailTrace_435836
  have hstable : (prefixWord ++ tailWord_435836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435836).length < 2 ^ (prefixWord ++ tailWord_435836).sum := by decide
  have hdescent : baseEnd_435836 < baseStart_435836 := by decide
  rcases family_descends (prefixWord ++ tailWord_435836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435911 : List Nat := [1, 1, 4, 1, 1, 1, 4, 2, 1, 6]
def baseStart_435911 : Nat := 118140960795 + 435911 * 2 ^ 59
def prefixEnd_435911 : Nat := 4983230072969 + 3 ^ 40 * 435911 * 2
def baseEnd_435911 : Nat := 149221243721432819938525

theorem tailTrace_435911 : CollatzResearch.WordTrace tailWord_435911 prefixEnd_435911 149221243721432819938525 := by
  unfold tailWord_435911
  simp only [CollatzResearch.WordTrace]
  refine ⟨15898980323776369516827587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10599320215850913011218391 15898980323776369516827587)
  ·
    refine ⟨23848470485664554275241381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15898980323776369516827587 23848470485664554275241381)
    ·
      refine ⟨4471588216062103926607759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23848470485664554275241381 4471588216062103926607759)
      ·
        refine ⟨6707382324093155889911639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4471588216062103926607759 6707382324093155889911639)
        ·
          refine ⟨10061073486139733834867459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6707382324093155889911639 10061073486139733834867459)
          ·
            refine ⟨15091610229209600752301189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10061073486139733834867459 15091610229209600752301189)
            ·
              refine ⟨2829676917976800141056473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15091610229209600752301189 2829676917976800141056473)
              ·
                refine ⟨2122257688482600105792355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2829676917976800141056473 2122257688482600105792355)
                ·
                  refine ⟨3183386532723900158688533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2122257688482600105792355 3183386532723900158688533)
                  ·
                    refine ⟨149221243721432819938525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3183386532723900158688533 149221243721432819938525)
                    ·
                      rfl

theorem cell22_435911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_435911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_435911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_435911 prefixEnd_435911 := by exact prefixLift 435911
  have htrace : WordTrace (prefixWord ++ tailWord_435911) baseStart_435911 baseEnd_435911 := by
    simpa [prefixWord, tailWord_435911, baseEnd_435911] using wordTrace_append hprefix tailTrace_435911
  have hstable : (prefixWord ++ tailWord_435911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435911).length < 2 ^ (prefixWord ++ tailWord_435911).sum := by decide
  have hdescent : baseEnd_435911 < baseStart_435911 := by decide
  rcases family_descends (prefixWord ++ tailWord_435911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435992 : List Nat := [2, 1, 2, 3, 1, 1, 5, 3, 1, 3]
def baseStart_435992 : Nat := 118140960795 + 435992 * 2 ^ 59
def prefixEnd_435992 : Nat := 4983230072969 + 3 ^ 40 * 435992 * 2
def baseEnd_435992 : Nat := 149248971676775608663277

theorem tailTrace_435992 : CollatzResearch.WordTrace tailWord_435992 prefixEnd_435992 149248971676775608663277 := by
  unfold tailWord_435992
  simp only [CollatzResearch.WordTrace]
  refine ⟨7950967318241460175263115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10601289757655280233684153 7950967318241460175263115)
  ·
    refine ⟨11926450977362190262894673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7950967318241460175263115 11926450977362190262894673)
    ·
      refine ⟨8944838233021642697171005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11926450977362190262894673 8944838233021642697171005)
      ·
        refine ⟨3354314337383116011439127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8944838233021642697171005 3354314337383116011439127)
        ·
          refine ⟨5031471506074674017158691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3354314337383116011439127 5031471506074674017158691)
          ·
            refine ⟨7547207259112011025738037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5031471506074674017158691 7547207259112011025738037)
            ·
              refine ⟨707550680541751033662941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7547207259112011025738037 707550680541751033662941)
              ·
                refine ⟨265331505203156637623603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 707550680541751033662941 265331505203156637623603)
                ·
                  refine ⟨397997257804734956435405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 265331505203156637623603 397997257804734956435405)
                  ·
                    refine ⟨149248971676775608663277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 397997257804734956435405 149248971676775608663277)
                    ·
                      rfl

theorem cell22_435992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 3, 1, 3].length) (baseStart_435992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_435992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_435992 prefixEnd_435992 := by exact prefixLift 435992
  have htrace : WordTrace (prefixWord ++ tailWord_435992) baseStart_435992 baseEnd_435992 := by
    simpa [prefixWord, tailWord_435992, baseEnd_435992] using wordTrace_append hprefix tailTrace_435992
  have hstable : (prefixWord ++ tailWord_435992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435992).length < 2 ^ (prefixWord ++ tailWord_435992).sum := by decide
  have hdescent : baseEnd_435992 < baseStart_435992 := by decide
  rcases family_descends (prefixWord ++ tailWord_435992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436022 : List Nat := [5, 1, 2, 2, 1, 2, 1, 3, 5]
def baseStart_436022 : Nat := 118140960795 + 436022 * 2 ^ 59
def prefixEnd_436022 : Nat := 4983230072969 + 3 ^ 40 * 436022 * 2
def baseEnd_436022 : Nat := 49753080429955176804395

theorem tailTrace_436022 : CollatzResearch.WordTrace tailWord_436022 prefixEnd_436022 49753080429955176804395 := by
  unfold tailWord_436022
  simp only [CollatzResearch.WordTrace]
  refine ⟨993939301648389717132395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10602019217582823649412213 993939301648389717132395)
  ·
    refine ⟨1490908952472584575698593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 993939301648389717132395 1490908952472584575698593)
    ·
      refine ⟨1118181714354438431773945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1490908952472584575698593 1118181714354438431773945)
      ·
        refine ⟨838636285765828823830459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1118181714354438431773945 838636285765828823830459)
        ·
          refine ⟨1257954428648743235745689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 838636285765828823830459 1257954428648743235745689)
          ·
            refine ⟨943465821486557426809267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1257954428648743235745689 943465821486557426809267)
            ·
              refine ⟨1415198732229836140213901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 943465821486557426809267 1415198732229836140213901)
              ·
                refine ⟨530699524586188552580213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1415198732229836140213901 530699524586188552580213)
                ·
                  refine ⟨49753080429955176804395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 530699524586188552580213 49753080429955176804395)
                  ·
                    rfl

theorem cell22_436022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_436022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_436022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_436022 prefixEnd_436022 := by exact prefixLift 436022
  have htrace : WordTrace (prefixWord ++ tailWord_436022) baseStart_436022 baseEnd_436022 := by
    simpa [prefixWord, tailWord_436022, baseEnd_436022] using wordTrace_append hprefix tailTrace_436022
  have hstable : (prefixWord ++ tailWord_436022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436022).length < 2 ^ (prefixWord ++ tailWord_436022).sum := by decide
  have hdescent : baseEnd_436022 < baseStart_436022 := by decide
  rcases family_descends (prefixWord ++ tailWord_436022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436035 : List Nat := [1, 1, 1, 3, 1, 5, 3, 2, 1, 4]
def baseStart_436035 : Nat := 118140960795 + 436035 * 2 ^ 59
def prefixEnd_436035 : Nat := 4983230072969 + 3 ^ 40 * 436035 * 2
def baseEnd_436035 : Nat := 149263691455537829838145

theorem tailTrace_436035 : CollatzResearch.WordTrace tailWord_436035 prefixEnd_436035 149263691455537829838145 := by
  unfold tailWord_436035
  simp only [CollatzResearch.WordTrace]
  refine ⟨15903502975327138694341559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10602335316884759129561039 15903502975327138694341559)
  ·
    refine ⟨23855254462990708041512339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15903502975327138694341559 23855254462990708041512339)
    ·
      refine ⟨35782881694486062062268509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23855254462990708041512339 35782881694486062062268509)
      ·
        refine ⟨13418580635432273273350691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35782881694486062062268509 13418580635432273273350691)
        ·
          refine ⟨20127870953148409910026037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13418580635432273273350691 20127870953148409910026037)
          ·
            refine ⟨1886987901857663429064941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20127870953148409910026037 1886987901857663429064941)
            ·
              refine ⟨707620463196623785899353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1886987901857663429064941 707620463196623785899353)
              ·
                refine ⟨530715347397467839424515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 707620463196623785899353 530715347397467839424515)
                ·
                  refine ⟨796073021096201759136773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 530715347397467839424515 796073021096201759136773)
                  ·
                    refine ⟨149263691455537829838145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 796073021096201759136773 149263691455537829838145)
                    ·
                      rfl

theorem cell22_436035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 2, 1, 4].length) (baseStart_436035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_436035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_436035 prefixEnd_436035 := by exact prefixLift 436035
  have htrace : WordTrace (prefixWord ++ tailWord_436035) baseStart_436035 baseEnd_436035 := by
    simpa [prefixWord, tailWord_436035, baseEnd_436035] using wordTrace_append hprefix tailTrace_436035
  have hstable : (prefixWord ++ tailWord_436035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436035).length < 2 ^ (prefixWord ++ tailWord_436035).sum := by decide
  have hdescent : baseEnd_436035 < baseStart_436035 := by decide
  rcases family_descends (prefixWord ++ tailWord_436035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436067 : List Nat := [1, 1, 1, 5, 4, 1, 1, 4, 4]
def baseStart_436067 : Nat := 118140960795 + 436067 * 2 ^ 59
def prefixEnd_436067 : Nat := 4983230072969 + 3 ^ 40 * 436067 * 2
def baseEnd_436067 : Nat := 49758215236500137679349

theorem tailTrace_436067 : CollatzResearch.WordTrace tailWord_436067 prefixEnd_436067 49758215236500137679349 := by
  unfold tailWord_436067
  simp only [CollatzResearch.WordTrace]
  refine ⟨15904670111211208159506455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10603113407474138773004303 15904670111211208159506455)
  ·
    refine ⟨23857005166816812239259683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15904670111211208159506455 23857005166816812239259683)
    ·
      refine ⟨35785507750225218358889525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23857005166816812239259683 35785507750225218358889525)
      ·
        refine ⟨3354891351583614221145893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35785507750225218358889525 3354891351583614221145893)
        ·
          refine ⟨629042128421927666464855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3354891351583614221145893 629042128421927666464855)
          ·
            refine ⟨943563192632891499697283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 629042128421927666464855 943563192632891499697283)
            ·
              refine ⟨1415344788949337249545925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 943563192632891499697283 1415344788949337249545925)
              ·
                refine ⟨265377147928000734289861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1415344788949337249545925 265377147928000734289861)
                ·
                  refine ⟨49758215236500137679349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 265377147928000734289861 49758215236500137679349)
                  ·
                    rfl

theorem cell22_436067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 4, 4].length) (baseStart_436067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_436067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_436067 prefixEnd_436067 := by exact prefixLift 436067
  have htrace : WordTrace (prefixWord ++ tailWord_436067) baseStart_436067 baseEnd_436067 := by
    simpa [prefixWord, tailWord_436067, baseEnd_436067] using wordTrace_append hprefix tailTrace_436067
  have hstable : (prefixWord ++ tailWord_436067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436067).length < 2 ^ (prefixWord ++ tailWord_436067).sum := by decide
  have hdescent : baseEnd_436067 < baseStart_436067 := by decide
  rcases family_descends (prefixWord ++ tailWord_436067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436097 : List Nat := [1, 2, 4, 4, 1, 1, 1, 1, 1, 6]
def baseStart_436097 : Nat := 118140960795 + 436097 * 2 ^ 59
def prefixEnd_436097 : Nat := 4983230072969 + 3 ^ 40 * 436097 * 2
def baseEnd_436097 : Nat := 149284915322590334787955

theorem tailTrace_436097 : CollatzResearch.WordTrace tailWord_436097 prefixEnd_436097 149284915322590334787955 := by
  unfold tailWord_436097
  simp only [CollatzResearch.WordTrace]
  refine ⟨15905764301102523283098545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10603842867401682188732363 15905764301102523283098545)
  ·
    refine ⟨11929323225826892462323909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15905764301102523283098545 11929323225826892462323909)
    ·
      refine ⟨2236748104842542336685733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11929323225826892462323909 2236748104842542336685733)
      ·
        refine ⟨419390269657976688128575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2236748104842542336685733 419390269657976688128575)
        ·
          refine ⟨629085404486965032192863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 419390269657976688128575 629085404486965032192863)
          ·
            refine ⟨943628106730447548289295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 629085404486965032192863 943628106730447548289295)
            ·
              refine ⟨1415442160095671322433943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 943628106730447548289295 1415442160095671322433943)
              ·
                refine ⟨2123163240143506983650915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1415442160095671322433943 2123163240143506983650915)
                ·
                  refine ⟨3184744860215260475476373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2123163240143506983650915 3184744860215260475476373)
                  ·
                    refine ⟨149284915322590334787955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3184744860215260475476373 149284915322590334787955)
                    ·
                      rfl

theorem cell22_436097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_436097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_436097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_436097 prefixEnd_436097 := by exact prefixLift 436097
  have htrace : WordTrace (prefixWord ++ tailWord_436097) baseStart_436097 baseEnd_436097 := by
    simpa [prefixWord, tailWord_436097, baseEnd_436097] using wordTrace_append hprefix tailTrace_436097
  have hstable : (prefixWord ++ tailWord_436097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436097).length < 2 ^ (prefixWord ++ tailWord_436097).sum := by decide
  have hdescent : baseEnd_436097 < baseStart_436097 := by decide
  rcases family_descends (prefixWord ++ tailWord_436097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436178 : List Nat := [3, 2, 2, 3, 2, 1, 3, 2, 1, 3]
def baseStart_436178 : Nat := 118140960795 + 436178 * 2 ^ 59
def prefixEnd_436178 : Nat := 4983230072969 + 3 ^ 40 * 436178 * 2
def baseEnd_436178 : Nat := 149312643277933123512707

theorem tailTrace_436178 : CollatzResearch.WordTrace tailWord_436178 prefixEnd_436178 149312643277933123512707 := by
  unfold tailWord_436178
  simp only [CollatzResearch.WordTrace]
  refine ⟨3977179653452268529199297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10605812409206049411198125 3977179653452268529199297)
  ·
    refine ⟨2982884740089201396899473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3977179653452268529199297 2982884740089201396899473)
    ·
      refine ⟨2237163555066901047674605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2982884740089201396899473 2237163555066901047674605)
      ·
        refine ⟨838936333150087892877977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2237163555066901047674605 838936333150087892877977)
        ·
          refine ⟨629202249862565919658483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 838936333150087892877977 629202249862565919658483)
          ·
            refine ⟨943803374793848879487725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 629202249862565919658483 943803374793848879487725)
            ·
              refine ⟨353926265547693329807897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 943803374793848879487725 353926265547693329807897)
              ·
                refine ⟨265444699160769997355923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 353926265547693329807897 265444699160769997355923)
                ·
                  refine ⟨398167048741154996033885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 265444699160769997355923 398167048741154996033885)
                  ·
                    refine ⟨149312643277933123512707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 398167048741154996033885 149312643277933123512707)
                    ·
                      rfl

theorem cell22_436178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3, 2, 1, 3].length) (baseStart_436178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_436178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_436178 prefixEnd_436178 := by exact prefixLift 436178
  have htrace : WordTrace (prefixWord ++ tailWord_436178) baseStart_436178 baseEnd_436178 := by
    simpa [prefixWord, tailWord_436178, baseEnd_436178] using wordTrace_append hprefix tailTrace_436178
  have hstable : (prefixWord ++ tailWord_436178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436178).length < 2 ^ (prefixWord ++ tailWord_436178).sum := by decide
  have hdescent : baseEnd_436178 < baseStart_436178 := by decide
  rcases family_descends (prefixWord ++ tailWord_436178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436200 : List Nat := [2, 1, 4, 1, 1, 1, 1, 5, 1, 5]
def baseStart_436200 : Nat := 118140960795 + 436200 * 2 ^ 59
def prefixEnd_436200 : Nat := 4983230072969 + 3 ^ 40 * 436200 * 2
def baseEnd_436200 : Nat := 149320174327532399462639

theorem tailTrace_436200 : CollatzResearch.WordTrace tailWord_436200 prefixEnd_436200 149320174327532399462639 := by
  unfold tailWord_436200
  simp only [CollatzResearch.WordTrace]
  refine ⟨7954760509864685937049027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10606347346486247916065369 7954760509864685937049027)
  ·
    refine ⟨11932140764797028905573541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7954760509864685937049027 11932140764797028905573541)
    ·
      refine ⟨2237276393399442919795039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11932140764797028905573541 2237276393399442919795039)
      ·
        refine ⟨3355914590099164379692559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2237276393399442919795039 3355914590099164379692559)
        ·
          refine ⟨5033871885148746569538839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3355914590099164379692559 5033871885148746569538839)
          ·
            refine ⟨7550807827723119854308259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5033871885148746569538839 7550807827723119854308259)
            ·
              refine ⟨11326211741584679781462389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7550807827723119854308259 11326211741584679781462389)
              ·
                refine ⟨1061832350773563729512099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11326211741584679781462389 1061832350773563729512099)
                ·
                  refine ⟨1592748526160345594268149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1061832350773563729512099 1592748526160345594268149)
                  ·
                    refine ⟨149320174327532399462639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1592748526160345594268149 149320174327532399462639)
                    ·
                      rfl

theorem cell22_436200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_436200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_436200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_436200 prefixEnd_436200 := by exact prefixLift 436200
  have htrace : WordTrace (prefixWord ++ tailWord_436200) baseStart_436200 baseEnd_436200 := by
    simpa [prefixWord, tailWord_436200, baseEnd_436200] using wordTrace_append hprefix tailTrace_436200
  have hstable : (prefixWord ++ tailWord_436200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436200).length < 2 ^ (prefixWord ++ tailWord_436200).sum := by decide
  have hdescent : baseEnd_436200 < baseStart_436200 := by decide
  rcases family_descends (prefixWord ++ tailWord_436200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436279 : List Nat := [1, 1, 3, 1, 2, 2, 3, 5, 1, 3]
def baseStart_436279 : Nat := 118140960795 + 436279 * 2 ^ 59
def prefixEnd_436279 : Nat := 4983230072969 + 3 ^ 40 * 436279 * 2
def baseEnd_436279 : Nat := 149347217642002526737397

theorem tailTrace_436279 : CollatzResearch.WordTrace tailWord_436279 prefixEnd_436279 149347217642002526737397 := by
  unfold tailWord_436279
  simp only [CollatzResearch.WordTrace]
  refine ⟨15912402386443168366223891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10608268257628778910815927 15912402386443168366223891)
  ·
    refine ⟨23868603579664752549335837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15912402386443168366223891 23868603579664752549335837)
    ·
      refine ⟨8950726342374282206000939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23868603579664752549335837 8950726342374282206000939)
      ·
        refine ⟨13426089513561423309001409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8950726342374282206000939 13426089513561423309001409)
        ·
          refine ⟨10069567135171067481751057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13426089513561423309001409 10069567135171067481751057)
          ·
            refine ⟨7552175351378300611313293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10069567135171067481751057 7552175351378300611313293)
            ·
              refine ⟨2832065756766862729242485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7552175351378300611313293 2832065756766862729242485)
              ·
                refine ⟨265506164696893380866483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2832065756766862729242485 265506164696893380866483)
                ·
                  refine ⟨398259247045340071299725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 265506164696893380866483 398259247045340071299725)
                  ·
                    refine ⟨149347217642002526737397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 398259247045340071299725 149347217642002526737397)
                    ·
                      rfl

theorem cell22_436279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 5, 1, 3].length) (baseStart_436279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_436279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_436279 prefixEnd_436279 := by exact prefixLift 436279
  have htrace : WordTrace (prefixWord ++ tailWord_436279) baseStart_436279 baseEnd_436279 := by
    simpa [prefixWord, tailWord_436279, baseEnd_436279] using wordTrace_append hprefix tailTrace_436279
  have hstable : (prefixWord ++ tailWord_436279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436279).length < 2 ^ (prefixWord ++ tailWord_436279).sum := by decide
  have hdescent : baseEnd_436279 < baseStart_436279 := by decide
  rcases family_descends (prefixWord ++ tailWord_436279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436309 : List Nat := [1, 3, 2, 2, 1, 4, 3, 1, 5]
def baseStart_436309 : Nat := 118140960795 + 436309 * 2 ^ 59
def prefixEnd_436309 : Nat := 4983230072969 + 3 ^ 40 * 436309 * 2
def baseEnd_436309 : Nat := 49785829085030816162435

theorem tailTrace_436309 : CollatzResearch.WordTrace tailWord_436309 prefixEnd_436309 49785829085030816162435 := by
  unfold tailWord_436309
  simp only [CollatzResearch.WordTrace]
  refine ⟨15913496576334483489815981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10608997717556322326543987 15913496576334483489815981)
  ·
    refine ⟨5967561216125431308680993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15913496576334483489815981 5967561216125431308680993)
    ·
      refine ⟨4475670912094073481510745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5967561216125431308680993 4475670912094073481510745)
      ·
        refine ⟨3356753184070555111133059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4475670912094073481510745 3356753184070555111133059)
        ·
          refine ⟨5035129776105832666699589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3356753184070555111133059 5035129776105832666699589)
          ·
            refine ⟨944086833019843625006173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5035129776105832666699589 944086833019843625006173)
            ·
              refine ⟨354032562382441359377315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 944086833019843625006173 354032562382441359377315)
              ·
                refine ⟨531048843573662039065973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 354032562382441359377315 531048843573662039065973)
                ·
                  refine ⟨49785829085030816162435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 531048843573662039065973 49785829085030816162435)
                  ·
                    rfl

theorem cell22_436309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3, 1, 5].length) (baseStart_436309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_436309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_436309 prefixEnd_436309 := by exact prefixLift 436309
  have htrace : WordTrace (prefixWord ++ tailWord_436309) baseStart_436309 baseEnd_436309 := by
    simpa [prefixWord, tailWord_436309, baseEnd_436309] using wordTrace_append hprefix tailTrace_436309
  have hstable : (prefixWord ++ tailWord_436309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436309).length < 2 ^ (prefixWord ++ tailWord_436309).sum := by decide
  have hdescent : baseEnd_436309 < baseStart_436309 := by decide
  rcases family_descends (prefixWord ++ tailWord_436309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436330 : List Nat := [3, 1, 3, 2, 4, 1, 1, 3, 1, 3]
def baseStart_436330 : Nat := 118140960795 + 436330 * 2 ^ 59
def prefixEnd_436330 : Nat := 4983230072969 + 3 ^ 40 * 436330 * 2
def baseEnd_436330 : Nat := 149364675984255393712241

theorem tailTrace_436330 : CollatzResearch.WordTrace tailWord_436330 prefixEnd_436330 149364675984255393712241 := by
  unfold tailWord_436330
  simp only [CollatzResearch.WordTrace]
  refine ⟨3978565627314601019082611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10609508339505602717553629 3978565627314601019082611)
  ·
    refine ⟨5967848440971901528623917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3978565627314601019082611 5967848440971901528623917)
    ·
      refine ⟨2237943165364463073233969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5967848440971901528623917 2237943165364463073233969)
      ·
        refine ⟨1678457374023347304925477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2237943165364463073233969 1678457374023347304925477)
        ·
          refine ⟨314710757629377619673527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1678457374023347304925477 314710757629377619673527)
          ·
            refine ⟨472066136444066429510291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314710757629377619673527 472066136444066429510291)
            ·
              refine ⟨708099204666099644265437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 472066136444066429510291 708099204666099644265437)
              ·
                refine ⟨265537201749787366599539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 708099204666099644265437 265537201749787366599539)
                ·
                  refine ⟨398305802624681049899309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 265537201749787366599539 398305802624681049899309)
                  ·
                    refine ⟨149364675984255393712241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 398305802624681049899309 149364675984255393712241)
                    ·
                      rfl

theorem cell22_436330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 3, 1, 3].length) (baseStart_436330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_436330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_436330 prefixEnd_436330 := by exact prefixLift 436330
  have htrace : WordTrace (prefixWord ++ tailWord_436330) baseStart_436330 baseEnd_436330 := by
    simpa [prefixWord, tailWord_436330, baseEnd_436330] using wordTrace_append hprefix tailTrace_436330
  have hstable : (prefixWord ++ tailWord_436330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436330).length < 2 ^ (prefixWord ++ tailWord_436330).sum := by decide
  have hdescent : baseEnd_436330 < baseStart_436330 := by decide
  rcases family_descends (prefixWord ++ tailWord_436330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436384 : List Nat := [2, 1, 1, 4, 2, 3, 2, 1, 2, 4]
def baseStart_436384 : Nat := 118140960795 + 436384 * 2 ^ 59
def prefixEnd_436384 : Nat := 4983230072969 + 3 ^ 40 * 436384 * 2
def baseEnd_436384 : Nat := 149383161287817252862075

theorem tailTrace_436384 : CollatzResearch.WordTrace tailWord_436384 prefixEnd_436384 149383161287817252862075 := by
  unfold tailWord_436384
  simp only [CollatzResearch.WordTrace]
  refine ⟨7958116025531385649398103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10610821367375180865864137 7958116025531385649398103)
  ·
    refine ⟨11937174038297078474097155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7958116025531385649398103 11937174038297078474097155)
    ·
      refine ⟨17905761057445617711145733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11937174038297078474097155 17905761057445617711145733)
      ·
        refine ⟨3357330198271053320839825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17905761057445617711145733 3357330198271053320839825)
        ·
          refine ⟨2517997648703289990629869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3357330198271053320839825 2517997648703289990629869)
          ·
            refine ⟨944249118263733746486201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2517997648703289990629869 944249118263733746486201)
            ·
              refine ⟨708186838697800309864651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 944249118263733746486201 708186838697800309864651)
              ·
                refine ⟨1062280258046700464796977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 708186838697800309864651 1062280258046700464796977)
                ·
                  refine ⟨796710193535025348597733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1062280258046700464796977 796710193535025348597733)
                  ·
                    refine ⟨149383161287817252862075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 796710193535025348597733 149383161287817252862075)
                    ·
                      rfl

theorem cell22_436384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 1, 2, 4].length) (baseStart_436384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_436384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_436384 prefixEnd_436384 := by exact prefixLift 436384
  have htrace : WordTrace (prefixWord ++ tailWord_436384) baseStart_436384 baseEnd_436384 := by
    simpa [prefixWord, tailWord_436384, baseEnd_436384] using wordTrace_append hprefix tailTrace_436384
  have hstable : (prefixWord ++ tailWord_436384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436384).length < 2 ^ (prefixWord ++ tailWord_436384).sum := by decide
  have hdescent : baseEnd_436384 < baseStart_436384 := by decide
  rcases family_descends (prefixWord ++ tailWord_436384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436405 : List Nat := [1, 3, 3, 4, 1, 2, 2, 2, 4]
def baseStart_436405 : Nat := 118140960795 + 436405 * 2 ^ 59
def prefixEnd_436405 : Nat := 4983230072969 + 3 ^ 40 * 436405 * 2
def baseEnd_436405 : Nat := 49796783338993399362337

theorem tailTrace_436405 : CollatzResearch.WordTrace tailWord_436405 prefixEnd_436405 49796783338993399362337 := by
  unfold tailWord_436405
  simp only [CollatzResearch.WordTrace]
  refine ⟨15916997983986691885310669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10611331989324461256873779 15916997983986691885310669)
  ·
    refine ⟨5968874243995009456991501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15916997983986691885310669 5968874243995009456991501)
    ·
      refine ⟨2238327841498128546371813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5968874243995009456991501 2238327841498128546371813)
      ·
        refine ⟨419686470280899102444715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2238327841498128546371813 419686470280899102444715)
        ·
          refine ⟨629529705421348653667073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 419686470280899102444715 629529705421348653667073)
          ·
            refine ⟨472147279066011490250305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 629529705421348653667073 472147279066011490250305)
            ·
              refine ⟨354110459299508617687729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 472147279066011490250305 354110459299508617687729)
              ·
                refine ⟨265582844474631463265797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 354110459299508617687729 265582844474631463265797)
                ·
                  refine ⟨49796783338993399362337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 265582844474631463265797 49796783338993399362337)
                  ·
                    rfl

theorem cell22_436405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2, 2, 4].length) (baseStart_436405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_436405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_436405 prefixEnd_436405 := by exact prefixLift 436405
  have htrace : WordTrace (prefixWord ++ tailWord_436405) baseStart_436405 baseEnd_436405 := by
    simpa [prefixWord, tailWord_436405, baseEnd_436405] using wordTrace_append hprefix tailTrace_436405
  have hstable : (prefixWord ++ tailWord_436405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436405).length < 2 ^ (prefixWord ++ tailWord_436405).sum := by decide
  have hdescent : baseEnd_436405 < baseStart_436405 := by decide
  rcases family_descends (prefixWord ++ tailWord_436405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436427 : List Nat := [1, 1, 1, 1, 3, 2, 3, 5, 5]
def baseStart_436427 : Nat := 118140960795 + 436427 * 2 ^ 59
def prefixEnd_436427 : Nat := 4983230072969 + 3 ^ 40 * 436427 * 2
def baseEnd_436427 : Nat := 49799293688859824678981

theorem tailTrace_436427 : CollatzResearch.WordTrace tailWord_436427 prefixEnd_436427 49799293688859824678981 := by
  unfold tailWord_436427
  simp only [CollatzResearch.WordTrace]
  refine ⟨15917800389906989642611535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10611866926604659761741023 15917800389906989642611535)
  ·
    refine ⟨23876700584860484463917303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15917800389906989642611535 23876700584860484463917303)
    ·
      refine ⟨35815050877290726695875955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23876700584860484463917303 35815050877290726695875955)
      ·
        refine ⟨53722576315936090043813933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35815050877290726695875955 53722576315936090043813933)
        ·
          refine ⟨20145966118476033766430225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53722576315936090043813933 20145966118476033766430225)
          ·
            refine ⟨15109474588857025324822669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20145966118476033766430225 15109474588857025324822669)
            ·
              refine ⟨5666052970821384496808501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15109474588857025324822669 5666052970821384496808501)
              ·
                refine ⟨531192466014504796575797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5666052970821384496808501 531192466014504796575797)
                ·
                  refine ⟨49799293688859824678981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 531192466014504796575797 49799293688859824678981)
                  ·
                    rfl

theorem cell22_436427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 5, 5].length) (baseStart_436427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_436427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_436427 prefixEnd_436427 := by exact prefixLift 436427
  have htrace : WordTrace (prefixWord ++ tailWord_436427) baseStart_436427 baseEnd_436427 := by
    simpa [prefixWord, tailWord_436427, baseEnd_436427] using wordTrace_append hprefix tailTrace_436427
  have hstable : (prefixWord ++ tailWord_436427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436427).length < 2 ^ (prefixWord ++ tailWord_436427).sum := by decide
  have hdescent : baseEnd_436427 < baseStart_436427 := by decide
  rcases family_descends (prefixWord ++ tailWord_436427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436504 : List Nat := [2, 1, 2, 3, 1, 2, 1, 1, 6, 3]
def baseStart_436504 : Nat := 118140960795 + 436504 * 2 ^ 59
def prefixEnd_436504 : Nat := 4983230072969 + 3 ^ 40 * 436504 * 2
def baseEnd_436504 : Nat := 149424239740176939861707

theorem tailTrace_436504 : CollatzResearch.WordTrace tailWord_436504 prefixEnd_436504 149424239740176939861707 := by
  unfold tailWord_436504
  simp only [CollatzResearch.WordTrace]
  refine ⟨7960304405314015896582283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10613739207085354528776377 7960304405314015896582283)
  ·
    refine ⟨11940456607971023844873425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7960304405314015896582283 11940456607971023844873425)
    ·
      refine ⟨8955342455978267883655069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11940456607971023844873425 8955342455978267883655069)
      ·
        refine ⟨3358253420991850456370651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8955342455978267883655069 3358253420991850456370651)
        ·
          refine ⟨5037380131487775684555977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3358253420991850456370651 5037380131487775684555977)
          ·
            refine ⟨3778035098615831763416983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5037380131487775684555977 3778035098615831763416983)
            ·
              refine ⟨5667052647923747645125475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3778035098615831763416983 5667052647923747645125475)
              ·
                refine ⟨8500578971885621467688213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5667052647923747645125475 8500578971885621467688213)
                ·
                  refine ⟨398464639307138506297885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8500578971885621467688213 398464639307138506297885)
                  ·
                    refine ⟨149424239740176939861707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 398464639307138506297885 149424239740176939861707)
                    ·
                      rfl

theorem cell22_436504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 6, 3].length) (baseStart_436504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_436504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_436504 prefixEnd_436504 := by exact prefixLift 436504
  have htrace : WordTrace (prefixWord ++ tailWord_436504) baseStart_436504 baseEnd_436504 := by
    simpa [prefixWord, tailWord_436504, baseEnd_436504] using wordTrace_append hprefix tailTrace_436504
  have hstable : (prefixWord ++ tailWord_436504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436504).length < 2 ^ (prefixWord ++ tailWord_436504).sum := by decide
  have hdescent : baseEnd_436504 < baseStart_436504 := by decide
  rcases family_descends (prefixWord ++ tailWord_436504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436538 : List Nat := [3, 1, 1, 1, 4, 2, 4, 1, 2, 3]
def baseStart_436538 : Nat := 118140960795 + 436538 * 2 ^ 59
def prefixEnd_436538 : Nat := 4983230072969 + 3 ^ 40 * 436538 * 2
def baseEnd_436538 : Nat := 149435878635012184511603

theorem tailTrace_436538 : CollatzResearch.WordTrace tailWord_436538 prefixEnd_436538 149435878635012184511603 := by
  unfold tailWord_436538
  simp only [CollatzResearch.WordTrace]
  refine ⟨3980462223126213899975567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10614565928336570399934845 3980462223126213899975567)
  ·
    refine ⟨5970693334689320849963351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3980462223126213899975567 5970693334689320849963351)
    ·
      refine ⟨8956040002033981274945027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5970693334689320849963351 8956040002033981274945027)
      ·
        refine ⟨13434060003050971912417541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8956040002033981274945027 13434060003050971912417541)
        ·
          refine ⟨2518886250572057233578289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13434060003050971912417541 2518886250572057233578289)
          ·
            refine ⟨1889164687929042925183717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2518886250572057233578289 1889164687929042925183717)
            ·
              refine ⟨354218378986695548471947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1889164687929042925183717 354218378986695548471947)
              ·
                refine ⟨531327568480043322707921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 354218378986695548471947 531327568480043322707921)
                ·
                  refine ⟨398495676360032492030941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 531327568480043322707921 398495676360032492030941)
                  ·
                    refine ⟨149435878635012184511603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 398495676360032492030941 149435878635012184511603)
                    ·
                      rfl

theorem cell22_436538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4, 1, 2, 3].length) (baseStart_436538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_436538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_436538 prefixEnd_436538 := by exact prefixLift 436538
  have htrace : WordTrace (prefixWord ++ tailWord_436538) baseStart_436538 baseEnd_436538 := by
    simpa [prefixWord, tailWord_436538, baseEnd_436538] using wordTrace_append hprefix tailTrace_436538
  have hstable : (prefixWord ++ tailWord_436538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436538).length < 2 ^ (prefixWord ++ tailWord_436538).sum := by decide
  have hdescent : baseEnd_436538 < baseStart_436538 := by decide
  rcases family_descends (prefixWord ++ tailWord_436538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436574 : List Nat := [4, 4, 2, 1, 1, 1, 1, 4, 4]
def baseStart_436574 : Nat := 118140960795 + 436574 * 2 ^ 59
def prefixEnd_436574 : Nat := 4983230072969 + 3 ^ 40 * 436574 * 2
def baseEnd_436574 : Nat := 49816067390240030203831

theorem tailTrace_436574 : CollatzResearch.WordTrace tailWord_436574 prefixEnd_436574 49816067390240030203831 := by
  unfold tailWord_436574
  simp only [CollatzResearch.WordTrace]
  refine ⟨1990395240046804218526597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10615441280249622498808517 1990395240046804218526597)
  ·
    refine ⟨373199107508775790973737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1990395240046804218526597 373199107508775790973737)
    ·
      refine ⟨279899330631581843230303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373199107508775790973737 279899330631581843230303)
      ·
        refine ⟨419848995947372764845455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279899330631581843230303 419848995947372764845455)
        ·
          refine ⟨629773493921059147268183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 419848995947372764845455 629773493921059147268183)
          ·
            refine ⟨944660240881588720902275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 629773493921059147268183 944660240881588720902275)
            ·
              refine ⟨1416990361322383081353413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 944660240881588720902275 1416990361322383081353413)
              ·
                refine ⟨265685692747946827753765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1416990361322383081353413 265685692747946827753765)
                ·
                  refine ⟨49816067390240030203831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 265685692747946827753765 49816067390240030203831)
                  ·
                    rfl

theorem cell22_436574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_436574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_436574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_436574 prefixEnd_436574 := by exact prefixLift 436574
  have htrace : WordTrace (prefixWord ++ tailWord_436574) baseStart_436574 baseEnd_436574 := by
    simpa [prefixWord, tailWord_436574, baseEnd_436574] using wordTrace_append hprefix tailTrace_436574
  have hstable : (prefixWord ++ tailWord_436574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436574).length < 2 ^ (prefixWord ++ tailWord_436574).sum := by decide
  have hdescent : baseEnd_436574 < baseStart_436574 := by decide
  rcases family_descends (prefixWord ++ tailWord_436574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436594 : List Nat := [3, 2, 1, 2, 1, 3, 1, 1, 1, 7]
def baseStart_436594 : Nat := 118140960795 + 436594 * 2 ^ 59
def prefixEnd_436594 : Nat := 4983230072969 + 3 ^ 40 * 436594 * 2
def baseEnd_436594 : Nat := 149455048579446705111431

theorem tailTrace_436594 : CollatzResearch.WordTrace tailWord_436594 prefixEnd_436594 149455048579446705111431 := by
  unfold tailWord_436594
  simp only [CollatzResearch.WordTrace]
  refine ⟨3980972845075494290985209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10615927586867984775960557 3980972845075494290985209)
  ·
    refine ⟨2985729633806620718238907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3980972845075494290985209 2985729633806620718238907)
    ·
      refine ⟨4478594450709931077358361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2985729633806620718238907 4478594450709931077358361)
      ·
        refine ⟨3358945838032448308018771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4478594450709931077358361 3358945838032448308018771)
        ·
          refine ⟨5038418757048672462028157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3358945838032448308018771 5038418757048672462028157)
          ·
            refine ⟨1889407033893252173260559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5038418757048672462028157 1889407033893252173260559)
            ·
              refine ⟨2834110550839878259890839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1889407033893252173260559 2834110550839878259890839)
              ·
                refine ⟨4251165826259817389836259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2834110550839878259890839 4251165826259817389836259)
                ·
                  refine ⟨6376748739389726084754389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4251165826259817389836259 6376748739389726084754389)
                  ·
                    refine ⟨149455048579446705111431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6376748739389726084754389 149455048579446705111431)
                    ·
                      rfl

theorem cell22_436594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_436594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_436594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_436594 prefixEnd_436594 := by exact prefixLift 436594
  have htrace : WordTrace (prefixWord ++ tailWord_436594) baseStart_436594 baseEnd_436594 := by
    simpa [prefixWord, tailWord_436594, baseEnd_436594] using wordTrace_append hprefix tailTrace_436594
  have hstable : (prefixWord ++ tailWord_436594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436594).length < 2 ^ (prefixWord ++ tailWord_436594).sum := by decide
  have hdescent : baseEnd_436594 < baseStart_436594 := by decide
  rcases family_descends (prefixWord ++ tailWord_436594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436707 : List Nat := [1, 1, 1, 6, 3, 2, 2, 1, 2, 3]
def baseStart_436707 : Nat := 118140960795 + 436707 * 2 ^ 59
def prefixEnd_436707 : Nat := 4983230072969 + 3 ^ 40 * 436707 * 2
def baseEnd_436707 : Nat := 149493730788752077036085

theorem tailTrace_436707 : CollatzResearch.WordTrace tailWord_436707 prefixEnd_436707 149493730788752077036085 := by
  unfold tailWord_436707
  simp only [CollatzResearch.WordTrace]
  refine ⟨15928012828892597462804375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10618675219261731641869583 15928012828892597462804375)
  ·
    refine ⟨23892019243338896194206563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15928012828892597462804375 23892019243338896194206563)
    ·
      refine ⟨35838028865008344291309845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23892019243338896194206563 35838028865008344291309845)
      ·
        refine ⟨1679907603047266138655149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 35838028865008344291309845 1679907603047266138655149)
        ·
          refine ⟨629965351142724801995681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1679907603047266138655149 629965351142724801995681)
          ·
            refine ⟨472474013357043601496761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 629965351142724801995681 472474013357043601496761)
            ·
              refine ⟨354355510017782701122571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 472474013357043601496761 354355510017782701122571)
              ·
                refine ⟨531533265026674051683857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 354355510017782701122571 531533265026674051683857)
                ·
                  refine ⟨398649948770005538762893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 531533265026674051683857 398649948770005538762893)
                  ·
                    refine ⟨149493730788752077036085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 398649948770005538762893 149493730788752077036085)
                    ·
                      rfl

theorem cell22_436707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2, 1, 2, 3].length) (baseStart_436707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_436707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_436707 prefixEnd_436707 := by exact prefixLift 436707
  have htrace : WordTrace (prefixWord ++ tailWord_436707) baseStart_436707 baseEnd_436707 := by
    simpa [prefixWord, tailWord_436707, baseEnd_436707] using wordTrace_append hprefix tailTrace_436707
  have hstable : (prefixWord ++ tailWord_436707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436707).length < 2 ^ (prefixWord ++ tailWord_436707).sum := by decide
  have hdescent : baseEnd_436707 < baseStart_436707 := by decide
  rcases family_descends (prefixWord ++ tailWord_436707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436746 : List Nat := [3, 1, 2, 2, 2, 1, 2, 2, 2, 5]
def baseStart_436746 : Nat := 118140960795 + 436746 * 2 ^ 59
def prefixEnd_436746 : Nat := 4983230072969 + 3 ^ 40 * 436746 * 2
def baseEnd_436746 : Nat := 149507081285768975310965

theorem tailTrace_436746 : CollatzResearch.WordTrace tailWord_436746 prefixEnd_436746 149507081285768975310965 := by
  unfold tailWord_436746
  simp only [CollatzResearch.WordTrace]
  refine ⟨3982358818937826780868523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10619623517167538082316061 3982358818937826780868523)
  ·
    refine ⟨5973538228406740171302785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3982358818937826780868523 5973538228406740171302785)
    ·
      refine ⟨4480153671305055128477089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5973538228406740171302785 4480153671305055128477089)
      ·
        refine ⟨3360115253478791346357817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4480153671305055128477089 3360115253478791346357817)
        ·
          refine ⟨2520086440109093509768363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3360115253478791346357817 2520086440109093509768363)
          ·
            refine ⟨3780129660163640264652545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2520086440109093509768363 3780129660163640264652545)
            ·
              refine ⟨2835097245122730198489409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3780129660163640264652545 2835097245122730198489409)
              ·
                refine ⟨2126322933842047648867057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2835097245122730198489409 2126322933842047648867057)
                ·
                  refine ⟨1594742200381535736650293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2126322933842047648867057 1594742200381535736650293)
                  ·
                    refine ⟨149507081285768975310965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1594742200381535736650293 149507081285768975310965)
                    ·
                      rfl

theorem cell22_436746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_436746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_436746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_436746 prefixEnd_436746 := by exact prefixLift 436746
  have htrace : WordTrace (prefixWord ++ tailWord_436746) baseStart_436746 baseEnd_436746 := by
    simpa [prefixWord, tailWord_436746, baseEnd_436746] using wordTrace_append hprefix tailTrace_436746
  have hstable : (prefixWord ++ tailWord_436746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436746).length < 2 ^ (prefixWord ++ tailWord_436746).sum := by decide
  have hdescent : baseEnd_436746 < baseStart_436746 := by decide
  rcases family_descends (prefixWord ++ tailWord_436746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436748 : List Nat := [2, 2, 1, 2, 4, 2, 2, 2, 5]
def baseStart_436748 : Nat := 118140960795 + 436748 * 2 ^ 59
def prefixEnd_436748 : Nat := 4983230072969 + 3 ^ 40 * 436748 * 2
def baseEnd_436748 : Nat := 49835921975547212253653

theorem tailTrace_436748 : CollatzResearch.WordTrace tailWord_436748 prefixEnd_436748 49835921975547212253653 := by
  unfold tailWord_436748
  simp only [CollatzResearch.WordTrace]
  refine ⟨7964754110872030732523449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10619672147829374310031265 7964754110872030732523449)
  ·
    refine ⟨5973565583154023049392587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7964754110872030732523449 5973565583154023049392587)
    ·
      refine ⟨8960348374731034574088881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5973565583154023049392587 8960348374731034574088881)
      ·
        refine ⟨6720261281048275930566661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8960348374731034574088881 6720261281048275930566661)
        ·
          refine ⟨1260048990196551736981249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6720261281048275930566661 1260048990196551736981249)
          ·
            refine ⟨945036742647413802735937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1260048990196551736981249 945036742647413802735937)
            ·
              refine ⟨708777556985560352051953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 945036742647413802735937 708777556985560352051953)
              ·
                refine ⟨531583167739170264038965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 708777556985560352051953 531583167739170264038965)
                ·
                  refine ⟨49835921975547212253653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 531583167739170264038965 49835921975547212253653)
                  ·
                    rfl

theorem cell22_436748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 2, 5].length) (baseStart_436748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_436748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_436748 prefixEnd_436748 := by exact prefixLift 436748
  have htrace : WordTrace (prefixWord ++ tailWord_436748) baseStart_436748 baseEnd_436748 := by
    simpa [prefixWord, tailWord_436748, baseEnd_436748] using wordTrace_append hprefix tailTrace_436748
  have hstable : (prefixWord ++ tailWord_436748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436748).length < 2 ^ (prefixWord ++ tailWord_436748).sum := by decide
  have hdescent : baseEnd_436748 < baseStart_436748 := by decide
  rcases family_descends (prefixWord ++ tailWord_436748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436778 : List Nat := [3, 1, 4, 1, 1, 2, 2, 1, 3, 4]
def baseStart_436778 : Nat := 118140960795 + 436778 * 2 ^ 59
def prefixEnd_436778 : Nat := 4983230072969 + 3 ^ 40 * 436778 * 2
def baseEnd_436778 : Nat := 149518035539731558510867

theorem tailTrace_436778 : CollatzResearch.WordTrace tailWord_436778 prefixEnd_436778 149518035539731558510867 := by
  unfold tailWord_436778
  simp only [CollatzResearch.WordTrace]
  refine ⟨3982650602908844147159747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10620401607756917725759325 3982650602908844147159747)
  ·
    refine ⟨5973975904363266220739621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3982650602908844147159747 5973975904363266220739621)
    ·
      refine ⟨1120120482068112416388679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5973975904363266220739621 1120120482068112416388679)
      ·
        refine ⟨1680180723102168624583019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1120120482068112416388679 1680180723102168624583019)
        ·
          refine ⟨2520271084653252936874529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1680180723102168624583019 2520271084653252936874529)
          ·
            refine ⟨1890203313489939702655897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2520271084653252936874529 1890203313489939702655897)
            ·
              refine ⟨1417652485117454776991923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1890203313489939702655897 1417652485117454776991923)
              ·
                refine ⟨2126478727676182165487885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1417652485117454776991923 2126478727676182165487885)
                ·
                  refine ⟨797429522878568312057957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2126478727676182165487885 797429522878568312057957)
                  ·
                    refine ⟨149518035539731558510867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 797429522878568312057957 149518035539731558510867)
                    ·
                      rfl

theorem cell22_436778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_436778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_436778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_436778 prefixEnd_436778 := by exact prefixLift 436778
  have htrace : WordTrace (prefixWord ++ tailWord_436778) baseStart_436778 baseEnd_436778 := by
    simpa [prefixWord, tailWord_436778, baseEnd_436778] using wordTrace_append hprefix tailTrace_436778
  have hstable : (prefixWord ++ tailWord_436778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436778).length < 2 ^ (prefixWord ++ tailWord_436778).sum := by decide
  have hdescent : baseEnd_436778 < baseStart_436778 := by decide
  rcases family_descends (prefixWord ++ tailWord_436778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436791 : List Nat := [1, 1, 3, 1, 2, 3, 1, 4, 1, 5]
def baseStart_436791 : Nat := 118140960795 + 436791 * 2 ^ 59
def prefixEnd_436791 : Nat := 4983230072969 + 3 ^ 40 * 436791 * 2
def baseEnd_436791 : Nat := 149522485705403857935827

theorem tailTrace_436791 : CollatzResearch.WordTrace tailWord_436791 prefixEnd_436791 149522485705403857935827 := by
  unfold tailWord_436791
  simp only [CollatzResearch.WordTrace]
  refine ⟨15931076560588279808862227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10620717707058853205908151 15931076560588279808862227)
  ·
    refine ⟨23896614840882419713293341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15931076560588279808862227 23896614840882419713293341)
    ·
      refine ⟨8961230565330907392485003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23896614840882419713293341 8961230565330907392485003)
      ·
        refine ⟨13441845847996361088727505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8961230565330907392485003 13441845847996361088727505)
        ·
          refine ⟨10081384385997270816545629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13441845847996361088727505 10081384385997270816545629)
          ·
            refine ⟨3780519144748976556204611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10081384385997270816545629 3780519144748976556204611)
            ·
              refine ⟨5670778717123464834306917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3780519144748976556204611 5670778717123464834306917)
              ·
                refine ⟨1063271009460649656432547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5670778717123464834306917 1063271009460649656432547)
                ·
                  refine ⟨1594906514190974484648821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1063271009460649656432547 1594906514190974484648821)
                  ·
                    refine ⟨149522485705403857935827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1594906514190974484648821 149522485705403857935827)
                    ·
                      rfl

theorem cell22_436791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4, 1, 5].length) (baseStart_436791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_436791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_436791 prefixEnd_436791 := by exact prefixLift 436791
  have htrace : WordTrace (prefixWord ++ tailWord_436791) baseStart_436791 baseEnd_436791 := by
    simpa [prefixWord, tailWord_436791, baseEnd_436791] using wordTrace_append hprefix tailTrace_436791
  have hstable : (prefixWord ++ tailWord_436791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436791).length < 2 ^ (prefixWord ++ tailWord_436791).sum := by decide
  have hdescent : baseEnd_436791 < baseStart_436791 := by decide
  rcases family_descends (prefixWord ++ tailWord_436791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436836 : List Nat := [2, 3, 1, 1, 2, 2, 1, 1, 2, 7]
def baseStart_436836 : Nat := 118140960795 + 436836 * 2 ^ 59
def prefixEnd_436836 : Nat := 4983230072969 + 3 ^ 40 * 436836 * 2
def baseEnd_436836 : Nat := 149537890125038740560689

theorem tailTrace_436836 : CollatzResearch.WordTrace tailWord_436836 prefixEnd_436836 149537890125038740560689 := by
  unfold tailWord_436836
  simp only [CollatzResearch.WordTrace]
  refine ⟨7966358922712626247125181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10621811896950168329500241 7966358922712626247125181)
  ·
    refine ⟨2987384596017234842671943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7966358922712626247125181 2987384596017234842671943)
    ·
      refine ⟨4481076894025852264007915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2987384596017234842671943 4481076894025852264007915)
      ·
        refine ⟨6721615341038778396011873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4481076894025852264007915 6721615341038778396011873)
        ·
          refine ⟨5041211505779083797008905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6721615341038778396011873 5041211505779083797008905)
          ·
            refine ⟨3780908629334312847756679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5041211505779083797008905 3780908629334312847756679)
            ·
              refine ⟨5671362944001469271635019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3780908629334312847756679 5671362944001469271635019)
              ·
                refine ⟨8507044416002203907452529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5671362944001469271635019 8507044416002203907452529)
                ·
                  refine ⟨6380283312001652930589397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8507044416002203907452529 6380283312001652930589397)
                  ·
                    refine ⟨149537890125038740560689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6380283312001652930589397 149537890125038740560689)
                    ·
                      rfl

theorem cell22_436836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_436836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_436836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_436836 prefixEnd_436836 := by exact prefixLift 436836
  have htrace : WordTrace (prefixWord ++ tailWord_436836) baseStart_436836 baseEnd_436836 := by
    simpa [prefixWord, tailWord_436836, baseEnd_436836] using wordTrace_append hprefix tailTrace_436836
  have hstable : (prefixWord ++ tailWord_436836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436836).length < 2 ^ (prefixWord ++ tailWord_436836).sum := by decide
  have hdescent : baseEnd_436836 < baseStart_436836 := by decide
  rcases family_descends (prefixWord ++ tailWord_436836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436881 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 6, 5]
def baseStart_436881 : Nat := 118140960795 + 436881 * 2 ^ 59
def prefixEnd_436881 : Nat := 4983230072969 + 3 ^ 40 * 436881 * 2
def baseEnd_436881 : Nat := 149553294544673623185551

theorem tailTrace_436881 : CollatzResearch.WordTrace tailWord_436881 prefixEnd_436881 149553294544673623185551 := by
  unfold tailWord_436881
  simp only [CollatzResearch.WordTrace]
  refine ⟨15934359130262225179638497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10622906086841483453092331 15934359130262225179638497)
  ·
    refine ⟨11950769347696668884728873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15934359130262225179638497 11950769347696668884728873)
    ·
      refine ⟨8963077010772501663546655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11950769347696668884728873 8963077010772501663546655)
      ·
        refine ⟨13444615516158752495319983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8963077010772501663546655 13444615516158752495319983)
        ·
          refine ⟨20166923274238128742979975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13444615516158752495319983 20166923274238128742979975)
          ·
            refine ⟨30250384911357193114469963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20166923274238128742979975 30250384911357193114469963)
            ·
              refine ⟨45375577367035789671704945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30250384911357193114469963 45375577367035789671704945)
              ·
                refine ⟨34031683025276842253778709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45375577367035789671704945 34031683025276842253778709)
                ·
                  refine ⟨1595235141809851980645877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 34031683025276842253778709 1595235141809851980645877)
                  ·
                    refine ⟨149553294544673623185551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1595235141809851980645877 149553294544673623185551)
                    ·
                      rfl

theorem cell22_436881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 5].length) (baseStart_436881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_436881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_436881 prefixEnd_436881 := by exact prefixLift 436881
  have htrace : WordTrace (prefixWord ++ tailWord_436881) baseStart_436881 baseEnd_436881 := by
    simpa [prefixWord, tailWord_436881, baseEnd_436881] using wordTrace_append hprefix tailTrace_436881
  have hstable : (prefixWord ++ tailWord_436881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436881).length < 2 ^ (prefixWord ++ tailWord_436881).sum := by decide
  have hdescent : baseEnd_436881 < baseStart_436881 := by decide
  rcases family_descends (prefixWord ++ tailWord_436881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436943 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 8, 3]
def baseStart_436943 : Nat := 118140960795 + 436943 * 2 ^ 59
def prefixEnd_436943 : Nat := 4983230072969 + 3 ^ 40 * 436943 * 2
def baseEnd_436943 : Nat := 149574518411726128135361

theorem tailTrace_436943 : CollatzResearch.WordTrace tailWord_436943 prefixEnd_436943 149574518411726128135361 := by
  unfold tailWord_436943
  simp only [CollatzResearch.WordTrace]
  refine ⟨15936620456037609768395483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10624413637358406512263655 15936620456037609768395483)
  ·
    refine ⟨23904930684056414652593225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15936620456037609768395483 23904930684056414652593225)
    ·
      refine ⟨17928698013042310989444919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23904930684056414652593225 17928698013042310989444919)
      ·
        refine ⟨26893047019563466484167379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17928698013042310989444919 26893047019563466484167379)
        ·
          refine ⟨40339570529345199726251069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26893047019563466484167379 40339570529345199726251069)
          ·
            refine ⟨15127338948504449897344151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40339570529345199726251069 15127338948504449897344151)
            ·
              refine ⟨22691008422756674846016227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15127338948504449897344151 22691008422756674846016227)
              ·
                refine ⟨34036512634135012269024341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22691008422756674846016227 34036512634135012269024341)
                ·
                  refine ⟨398865382431269675027629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34036512634135012269024341 398865382431269675027629)
                  ·
                    refine ⟨149574518411726128135361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 398865382431269675027629 149574518411726128135361)
                    ·
                      rfl

theorem cell22_436943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 8, 3].length) (baseStart_436943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_436943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_436943 prefixEnd_436943 := by exact prefixLift 436943
  have htrace : WordTrace (prefixWord ++ tailWord_436943) baseStart_436943 baseEnd_436943 := by
    simpa [prefixWord, tailWord_436943, baseEnd_436943] using wordTrace_append hprefix tailTrace_436943
  have hstable : (prefixWord ++ tailWord_436943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436943).length < 2 ^ (prefixWord ++ tailWord_436943).sum := by decide
  have hdescent : baseEnd_436943 < baseStart_436943 := by decide
  rcases family_descends (prefixWord ++ tailWord_436943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436973 : List Nat := [1, 5, 1, 2, 1, 1, 11]
def baseStart_436973 : Nat := 118140960795 + 436973 * 2 ^ 59
def prefixEnd_436973 : Nat := 4983230072969 + 3 ^ 40 * 436973 * 2
def baseEnd_436973 : Nat := 5540177334252446292047

theorem tailTrace_436973 : CollatzResearch.WordTrace tailWord_436973 prefixEnd_436973 5540177334252446292047 := by
  unfold tailWord_436973
  simp only [CollatzResearch.WordTrace]
  refine ⟨15937714645928924891987573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10625143097285949927991715 15937714645928924891987573)
  ·
    refine ⟨1494160748055836708623835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15937714645928924891987573 1494160748055836708623835)
    ·
      refine ⟨2241241122083755062935753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1494160748055836708623835 2241241122083755062935753)
      ·
        refine ⟨1680930841562816297201815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2241241122083755062935753 1680930841562816297201815)
        ·
          refine ⟨2521396262344224445802723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1680930841562816297201815 2521396262344224445802723)
          ·
            refine ⟨3782094393516336668704085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2521396262344224445802723 3782094393516336668704085)
            ·
              refine ⟨5540177334252446292047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 3782094393516336668704085 5540177334252446292047)
              ·
                rfl

theorem cell22_436973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 11].length) (baseStart_436973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_436973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_436973 prefixEnd_436973 := by exact prefixLift 436973
  have htrace : WordTrace (prefixWord ++ tailWord_436973) baseStart_436973 baseEnd_436973 := by
    simpa [prefixWord, tailWord_436973, baseEnd_436973] using wordTrace_append hprefix tailTrace_436973
  have hstable : (prefixWord ++ tailWord_436973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436973).length < 2 ^ (prefixWord ++ tailWord_436973).sum := by decide
  have hdescent : baseEnd_436973 < baseStart_436973 := by decide
  rcases family_descends (prefixWord ++ tailWord_436973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437018 : List Nat := [3, 1, 1, 3, 2, 1, 1, 1, 9]
def baseStart_437018 : Nat := 118140960795 + 437018 * 2 ^ 59
def prefixEnd_437018 : Nat := 4983230072969 + 3 ^ 40 * 437018 * 2
def baseEnd_437018 : Nat := 49866730814816977503377

theorem tailTrace_437018 : CollatzResearch.WordTrace tailWord_437018 prefixEnd_437018 49866730814816977503377 := by
  unfold tailWord_437018
  simp only [CollatzResearch.WordTrace]
  refine ⟨3984838982691474394343927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10626237287177265051583805 3984838982691474394343927)
  ·
    refine ⟨5977258474037211591515891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3984838982691474394343927 5977258474037211591515891)
    ·
      refine ⟨8965887711055817387273837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5977258474037211591515891 8965887711055817387273837)
      ·
        refine ⟨3362207891645931520227689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8965887711055817387273837 3362207891645931520227689)
        ·
          refine ⟨2521655918734448640170767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3362207891645931520227689 2521655918734448640170767)
          ·
            refine ⟨3782483878101672960256151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2521655918734448640170767 3782483878101672960256151)
            ·
              refine ⟨5673725817152509440384227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3782483878101672960256151 5673725817152509440384227)
              ·
                refine ⟨8510588725728764160576341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5673725817152509440384227 8510588725728764160576341)
                ·
                  refine ⟨49866730814816977503377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 8510588725728764160576341 49866730814816977503377)
                  ·
                    rfl

theorem cell22_437018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 9].length) (baseStart_437018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_437018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_437018 prefixEnd_437018 := by exact prefixLift 437018
  have htrace : WordTrace (prefixWord ++ tailWord_437018) baseStart_437018 baseEnd_437018 := by
    simpa [prefixWord, tailWord_437018, baseEnd_437018] using wordTrace_append hprefix tailTrace_437018
  have hstable : (prefixWord ++ tailWord_437018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437018).length < 2 ^ (prefixWord ++ tailWord_437018).sum := by decide
  have hdescent : baseEnd_437018 < baseStart_437018 := by decide
  rcases family_descends (prefixWord ++ tailWord_437018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437063 : List Nat := [1, 1, 4, 1, 2, 1, 1, 3, 8]
def baseStart_437063 : Nat := 118140960795 + 437063 * 2 ^ 59
def prefixEnd_437063 : Nat := 4983230072969 + 3 ^ 40 * 437063 * 2
def baseEnd_437063 : Nat := 49871865621361938378331

theorem tailTrace_437063 : CollatzResearch.WordTrace tailWord_437063 prefixEnd_437063 49871865621361938378331 := by
  unfold tailWord_437063
  simp only [CollatzResearch.WordTrace]
  refine ⟨15940997215602870262763843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10627331477068580175175895 15940997215602870262763843)
  ·
    refine ⟨23911495823404305394145765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15940997215602870262763843 23911495823404305394145765)
    ·
      refine ⟨4483405466888307261402331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23911495823404305394145765 4483405466888307261402331)
      ·
        refine ⟨6725108200332460892103497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4483405466888307261402331 6725108200332460892103497)
        ·
          refine ⟨5043831150249345669077623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6725108200332460892103497 5043831150249345669077623)
          ·
            refine ⟨7565746725374018503616435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5043831150249345669077623 7565746725374018503616435)
            ·
              refine ⟨11348620088061027755424653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7565746725374018503616435 11348620088061027755424653)
              ·
                refine ⟨4255732533022885408284245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11348620088061027755424653 4255732533022885408284245)
                ·
                  refine ⟨49871865621361938378331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4255732533022885408284245 49871865621361938378331)
                  ·
                    rfl

theorem cell22_437063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 8].length) (baseStart_437063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_437063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_437063 prefixEnd_437063 := by exact prefixLift 437063
  have htrace : WordTrace (prefixWord ++ tailWord_437063) baseStart_437063 baseEnd_437063 := by
    simpa [prefixWord, tailWord_437063, baseEnd_437063] using wordTrace_append hprefix tailTrace_437063
  have hstable : (prefixWord ++ tailWord_437063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437063).length < 2 ^ (prefixWord ++ tailWord_437063).sum := by decide
  have hdescent : baseEnd_437063 < baseStart_437063 := by decide
  rcases family_descends (prefixWord ++ tailWord_437063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437065 : List Nat := [1, 2, 1, 1, 2, 6, 1, 1, 3, 4]
def baseStart_437065 : Nat := 118140960795 + 437065 * 2 ^ 59
def prefixEnd_437065 : Nat := 4983230072969 + 3 ^ 40 * 437065 * 2
def baseEnd_437065 : Nat := 149616281504958476584987

theorem tailTrace_437065 : CollatzResearch.WordTrace tailWord_437065 prefixEnd_437065 149616281504958476584987 := by
  unfold tailWord_437065
  simp only [CollatzResearch.WordTrace]
  refine ⟨15941070161595624604336649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10627380107730416402891099 15941070161595624604336649)
  ·
    refine ⟨11955802621196718453252487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15941070161595624604336649 11955802621196718453252487)
    ·
      refine ⟨17933703931795077679878731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11955802621196718453252487 17933703931795077679878731)
      ·
        refine ⟨26900555897692616519818097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17933703931795077679878731 26900555897692616519818097)
        ·
          refine ⟨20175416923269462389863573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26900555897692616519818097 20175416923269462389863573)
          ·
            refine ⟨945722668278256049524855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20175416923269462389863573 945722668278256049524855)
            ·
              refine ⟨1418584002417384074287283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 945722668278256049524855 1418584002417384074287283)
              ·
                refine ⟨2127876003626076111430925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1418584002417384074287283 2127876003626076111430925)
                ·
                  refine ⟨797953501359778541786597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2127876003626076111430925 797953501359778541786597)
                  ·
                    refine ⟨149616281504958476584987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 797953501359778541786597 149616281504958476584987)
                    ·
                      rfl

theorem cell22_437065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 3, 4].length) (baseStart_437065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_437065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_437065 prefixEnd_437065 := by exact prefixLift 437065
  have htrace : WordTrace (prefixWord ++ tailWord_437065) baseStart_437065 baseEnd_437065 := by
    simpa [prefixWord, tailWord_437065, baseEnd_437065] using wordTrace_append hprefix tailTrace_437065
  have hstable : (prefixWord ++ tailWord_437065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437065).length < 2 ^ (prefixWord ++ tailWord_437065).sum := by decide
  have hdescent : baseEnd_437065 < baseStart_437065 := by decide
  rcases family_descends (prefixWord ++ tailWord_437065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437090 : List Nat := [3, 3, 2, 1, 4, 1, 2, 2, 1, 3]
def baseStart_437090 : Nat := 118140960795 + 437090 * 2 ^ 59
def prefixEnd_437090 : Nat := 4983230072969 + 3 ^ 40 * 437090 * 2
def baseEnd_437090 : Nat := 149624839515866744709911

theorem tailTrace_437090 : CollatzResearch.WordTrace tailWord_437090 prefixEnd_437090 149624839515866744709911 := by
  unfold tailWord_437090
  simp only [CollatzResearch.WordTrace]
  refine ⟨3985495496626263468499181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10627987991003369249331149 3985495496626263468499181)
  ·
    refine ⟨1494560811234848800687193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3985495496626263468499181 1494560811234848800687193)
    ·
      refine ⟨1120920608426136600515395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1494560811234848800687193 1120920608426136600515395)
      ·
        refine ⟨1681380912639204900773093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1120920608426136600515395 1681380912639204900773093)
        ·
          refine ⟨315258921119850918894955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1681380912639204900773093 315258921119850918894955)
          ·
            refine ⟨472888381679776378342433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315258921119850918894955 472888381679776378342433)
            ·
              refine ⟨354666286259832283756825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 472888381679776378342433 354666286259832283756825)
              ·
                refine ⟨265999714694874212817619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 354666286259832283756825 265999714694874212817619)
                ·
                  refine ⟨398999572042311319226429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 265999714694874212817619 398999572042311319226429)
                  ·
                    refine ⟨149624839515866744709911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 398999572042311319226429 149624839515866744709911)
                    ·
                      rfl

theorem cell22_437090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_437090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_437090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_437090 prefixEnd_437090 := by exact prefixLift 437090
  have htrace : WordTrace (prefixWord ++ tailWord_437090) baseStart_437090 baseEnd_437090 := by
    simpa [prefixWord, tailWord_437090, baseEnd_437090] using wordTrace_append hprefix tailTrace_437090
  have hstable : (prefixWord ++ tailWord_437090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437090).length < 2 ^ (prefixWord ++ tailWord_437090).sum := by decide
  have hdescent : baseEnd_437090 < baseStart_437090 := by decide
  rcases family_descends (prefixWord ++ tailWord_437090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437127 : List Nat := [1, 1, 4, 2, 3, 1, 3, 1, 2, 4]
def baseStart_437127 : Nat := 118140960795 + 437127 * 2 ^ 59
def prefixEnd_437127 : Nat := 4983230072969 + 3 ^ 40 * 437127 * 2
def baseEnd_437127 : Nat := 149637505372010981534797

theorem tailTrace_437127 : CollatzResearch.WordTrace tailWord_437127 prefixEnd_437127 149637505372010981534797 := by
  unfold tailWord_437127
  simp only [CollatzResearch.WordTrace]
  refine ⟨15943331487371009193093635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10628887658247339462062423 15943331487371009193093635)
  ·
    refine ⟨23914997231056513789640453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15943331487371009193093635 23914997231056513789640453)
    ·
      refine ⟨4484061980823096335557585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23914997231056513789640453 4484061980823096335557585)
      ·
        refine ⟨3363046485617322251668189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4484061980823096335557585 3363046485617322251668189)
        ·
          refine ⟨1261142432106495844375571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3363046485617322251668189 1261142432106495844375571)
          ·
            refine ⟨1891713648159743766563357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1261142432106495844375571 1891713648159743766563357)
            ·
              refine ⟨709392618059903912461259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1891713648159743766563357 709392618059903912461259)
              ·
                refine ⟨1064088927089855868691889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 709392618059903912461259 1064088927089855868691889)
                ·
                  refine ⟨798066695317391901518917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1064088927089855868691889 798066695317391901518917)
                  ·
                    refine ⟨149637505372010981534797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 798066695317391901518917 149637505372010981534797)
                    ·
                      rfl

theorem cell22_437127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 1, 2, 4].length) (baseStart_437127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_437127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_437127 prefixEnd_437127 := by exact prefixLift 437127
  have htrace : WordTrace (prefixWord ++ tailWord_437127) baseStart_437127 baseEnd_437127 := by
    simpa [prefixWord, tailWord_437127, baseEnd_437127] using wordTrace_append hprefix tailTrace_437127
  have hstable : (prefixWord ++ tailWord_437127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437127).length < 2 ^ (prefixWord ++ tailWord_437127).sum := by decide
  have hdescent : baseEnd_437127 < baseStart_437127 := by decide
  rcases family_descends (prefixWord ++ tailWord_437127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437146 : List Nat := [3, 1, 1, 4, 3, 2, 1, 2, 2, 3]
def baseStart_437146 : Nat := 118140960795 + 437146 * 2 ^ 59
def prefixEnd_437146 : Nat := 4983230072969 + 3 ^ 40 * 437146 * 2
def baseEnd_437146 : Nat := 149644009460301265309739

theorem tailTrace_437146 : CollatzResearch.WordTrace tailWord_437146 prefixEnd_437146 149644009460301265309739 := by
  unfold tailWord_437146
  simp only [CollatzResearch.WordTrace]
  refine ⟨3986006118575543859508823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10629349649534783625356861 3986006118575543859508823)
  ·
    refine ⟨5979009177863315789263235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3986006118575543859508823 5979009177863315789263235)
    ·
      refine ⟨8968513766794973683894853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5979009177863315789263235 8968513766794973683894853)
      ·
        refine ⟨1681596331274057565730285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8968513766794973683894853 1681596331274057565730285)
        ·
          refine ⟨630598624227771587148857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1681596331274057565730285 630598624227771587148857)
          ·
            refine ⟨472948968170828690361643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 630598624227771587148857 472948968170828690361643)
            ·
              refine ⟨709423452256243035542465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 472948968170828690361643 709423452256243035542465)
              ·
                refine ⟨532067589192182276656849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 709423452256243035542465 532067589192182276656849)
                ·
                  refine ⟨399050691894136707492637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 532067589192182276656849 399050691894136707492637)
                  ·
                    refine ⟨149644009460301265309739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 399050691894136707492637 149644009460301265309739)
                    ·
                      rfl

theorem cell22_437146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 2, 2, 3].length) (baseStart_437146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_437146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_437146 prefixEnd_437146 := by exact prefixLift 437146
  have htrace : WordTrace (prefixWord ++ tailWord_437146) baseStart_437146 baseEnd_437146 := by
    simpa [prefixWord, tailWord_437146, baseEnd_437146] using wordTrace_append hprefix tailTrace_437146
  have hstable : (prefixWord ++ tailWord_437146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437146).length < 2 ^ (prefixWord ++ tailWord_437146).sum := by decide
  have hdescent : baseEnd_437146 < baseStart_437146 := by decide
  rcases family_descends (prefixWord ++ tailWord_437146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437200 : List Nat := [2, 1, 1, 1, 1, 2, 3, 2, 5, 4]
def baseStart_437200 : Nat := 118140960795 + 437200 * 2 ^ 59
def prefixEnd_437200 : Nat := 4983230072969 + 3 ^ 40 * 437200 * 2
def baseEnd_437200 : Nat := 149662494763863124459573

theorem tailTrace_437200 : CollatzResearch.WordTrace tailWord_437200 prefixEnd_437200 149662494763863124459573 := by
  unfold tailWord_437200
  simp only [CollatzResearch.WordTrace]
  refine ⟨7972997008053271330250527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10630662677404361773667369 7972997008053271330250527)
  ·
    refine ⟨11959495512079906995375791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7972997008053271330250527 11959495512079906995375791)
    ·
      refine ⟨17939243268119860493063687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11959495512079906995375791 17939243268119860493063687)
      ·
        refine ⟨26908864902179790739595531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17939243268119860493063687 26908864902179790739595531)
        ·
          refine ⟨40363297353269686109393297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26908864902179790739595531 40363297353269686109393297)
          ·
            refine ⟨30272473014952264582044973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40363297353269686109393297 30272473014952264582044973)
            ·
              refine ⟨11352177380607099218266865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30272473014952264582044973 11352177380607099218266865)
              ·
                refine ⟨8514133035455324413700149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11352177380607099218266865 8514133035455324413700149)
                ·
                  refine ⟨798199972073936663784389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8514133035455324413700149 798199972073936663784389)
                  ·
                    refine ⟨149662494763863124459573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 798199972073936663784389 149662494763863124459573)
                    ·
                      rfl

theorem cell22_437200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 5, 4].length) (baseStart_437200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_437200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_437200 prefixEnd_437200 := by exact prefixLift 437200
  have htrace : WordTrace (prefixWord ++ tailWord_437200) baseStart_437200 baseEnd_437200 := by
    simpa [prefixWord, tailWord_437200, baseEnd_437200] using wordTrace_append hprefix tailTrace_437200
  have hstable : (prefixWord ++ tailWord_437200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437200).length < 2 ^ (prefixWord ++ tailWord_437200).sum := by decide
  have hdescent : baseEnd_437200 < baseStart_437200 := by decide
  rcases family_descends (prefixWord ++ tailWord_437200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437260 : List Nat := [2, 2, 1, 2, 3, 12]
def baseStart_437260 : Nat := 118140960795 + 437260 * 2 ^ 59
def prefixEnd_437260 : Nat := 4983230072969 + 3 ^ 40 * 437260 * 2
def baseEnd_437260 : Nat := 1847938691235098369869

theorem tailTrace_437260 : CollatzResearch.WordTrace tailWord_437260 prefixEnd_437260 1847938691235098369869 := by
  unfold tailWord_437260
  simp only [CollatzResearch.WordTrace]
  refine ⟨7974091197944586453842617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10632121597259448605123489 7974091197944586453842617)
  ·
    refine ⟨5980568398458439840381963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7974091197944586453842617 5980568398458439840381963)
    ·
      refine ⟨8970852597687659760572945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5980568398458439840381963 8970852597687659760572945)
      ·
        refine ⟨6728139448265744820429709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8970852597687659760572945 6728139448265744820429709)
        ·
          refine ⟨2523052293099654307661141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6728139448265744820429709 2523052293099654307661141)
          ·
            refine ⟨1847938691235098369869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 2523052293099654307661141 1847938691235098369869)
            ·
              rfl

theorem cell22_437260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 12].length) (baseStart_437260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_437260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_437260 prefixEnd_437260 := by exact prefixLift 437260
  have htrace : WordTrace (prefixWord ++ tailWord_437260) baseStart_437260 baseEnd_437260 := by
    simpa [prefixWord, tailWord_437260, baseEnd_437260] using wordTrace_append hprefix tailTrace_437260
  have hstable : (prefixWord ++ tailWord_437260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437260).length < 2 ^ (prefixWord ++ tailWord_437260).sum := by decide
  have hdescent : baseEnd_437260 < baseStart_437260 := by decide
  rcases family_descends (prefixWord ++ tailWord_437260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437294 : List Nat := [4, 1, 3, 1, 1, 1, 5, 6]
def baseStart_437294 : Nat := 118140960795 + 437294 * 2 ^ 59
def prefixEnd_437294 : Nat := 4983230072969 + 3 ^ 40 * 437294 * 2
def baseEnd_437294 : Nat := 16632741431653134734365

theorem tailTrace_437294 : CollatzResearch.WordTrace tailWord_437294 prefixEnd_437294 16632741431653134734365 := by
  unfold tailWord_437294
  simp only [CollatzResearch.WordTrace]
  refine ⟨1993677809720749589302867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10632948318510664476281957 1993677809720749589302867)
  ·
    refine ⟨2990516714581124383954301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1993677809720749589302867 2990516714581124383954301)
    ·
      refine ⟨1121443767967921643982863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2990516714581124383954301 1121443767967921643982863)
      ·
        refine ⟨1682165651951882465974295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1121443767967921643982863 1682165651951882465974295)
        ·
          refine ⟨2523248477927823698961443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1682165651951882465974295 2523248477927823698961443)
          ·
            refine ⟨3784872716891735548442165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2523248477927823698961443 3784872716891735548442165)
            ·
              refine ⟨354831817208600207666453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3784872716891735548442165 354831817208600207666453)
              ·
                refine ⟨16632741431653134734365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 354831817208600207666453 16632741431653134734365)
                ·
                  rfl

theorem cell22_437294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5, 6].length) (baseStart_437294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_437294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_437294 prefixEnd_437294 := by exact prefixLift 437294
  have htrace : WordTrace (prefixWord ++ tailWord_437294) baseStart_437294 baseEnd_437294 := by
    simpa [prefixWord, tailWord_437294, baseEnd_437294] using wordTrace_append hprefix tailTrace_437294
  have hstable : (prefixWord ++ tailWord_437294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437294).length < 2 ^ (prefixWord ++ tailWord_437294).sum := by decide
  have hdescent : baseEnd_437294 < baseStart_437294 := by decide
  rcases family_descends (prefixWord ++ tailWord_437294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437326 : List Nat := [4, 1, 1, 1, 1, 3, 1, 6, 1, 3]
def baseStart_437326 : Nat := 118140960795 + 437326 * 2 ^ 59
def prefixEnd_437326 : Nat := 4983230072969 + 3 ^ 40 * 437326 * 2
def baseEnd_437326 : Nat := 149705627138840795809187

theorem tailTrace_437326 : CollatzResearch.WordTrace tailWord_437326 prefixEnd_437326 149705627138840795809187 := by
  unfold tailWord_437326
  simp only [CollatzResearch.WordTrace]
  refine ⟨1993823701706258272448479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10633726409100044119725221 1993823701706258272448479)
  ·
    refine ⟨2990735552559387408672719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1993823701706258272448479 2990735552559387408672719)
    ·
      refine ⟨4486103328839081113009079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2990735552559387408672719 4486103328839081113009079)
      ·
        refine ⟨6729154993258621669513619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4486103328839081113009079 6729154993258621669513619)
        ·
          refine ⟨10093732489887932504270429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6729154993258621669513619 10093732489887932504270429)
          ·
            refine ⟨3785149683707974689101411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10093732489887932504270429 3785149683707974689101411)
            ·
              refine ⟨5677724525561962033652117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3785149683707974689101411 5677724525561962033652117)
              ·
                refine ⟨266143337135716970327443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5677724525561962033652117 266143337135716970327443)
                ·
                  refine ⟨399215005703575455491165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 266143337135716970327443 399215005703575455491165)
                  ·
                    refine ⟨149705627138840795809187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 399215005703575455491165 149705627138840795809187)
                    ·
                      rfl

theorem cell22_437326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 6, 1, 3].length) (baseStart_437326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_437326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_437326 prefixEnd_437326 := by exact prefixLift 437326
  have htrace : WordTrace (prefixWord ++ tailWord_437326) baseStart_437326 baseEnd_437326 := by
    simpa [prefixWord, tailWord_437326, baseEnd_437326] using wordTrace_append hprefix tailTrace_437326
  have hstable : (prefixWord ++ tailWord_437326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437326).length < 2 ^ (prefixWord ++ tailWord_437326).sum := by decide
  have hdescent : baseEnd_437326 < baseStart_437326 := by decide
  rcases family_descends (prefixWord ++ tailWord_437326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437397 : List Nat := [1, 3, 2, 1, 1, 1, 2, 4, 1, 6]
def baseStart_437397 : Nat := 118140960795 + 437397 * 2 ^ 59
def prefixEnd_437397 : Nat := 4983230072969 + 3 ^ 40 * 437397 * 2
def baseEnd_437397 : Nat := 149729931889820277283969

theorem tailTrace_437397 : CollatzResearch.WordTrace tailWord_437397 prefixEnd_437397 149729931889820277283969 := by
  unfold tailWord_437397
  simp only [CollatzResearch.WordTrace]
  refine ⟨15953179196392845305422445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10635452797595230203614963 15953179196392845305422445)
  ·
    refine ⟨5982442198647316989533417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15953179196392845305422445 5982442198647316989533417)
    ·
      refine ⟨4486831648985487742150063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5982442198647316989533417 4486831648985487742150063)
      ·
        refine ⟨6730247473478231613225095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4486831648985487742150063 6730247473478231613225095)
        ·
          refine ⟨10095371210217347419837643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6730247473478231613225095 10095371210217347419837643)
          ·
            refine ⟨15143056815326021129756465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10095371210217347419837643 15143056815326021129756465)
            ·
              refine ⟨11357292611494515847317349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15143056815326021129756465 11357292611494515847317349)
              ·
                refine ⟨2129492364655221721372003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11357292611494515847317349 2129492364655221721372003)
                ·
                  refine ⟨3194238546982832582058005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2129492364655221721372003 3194238546982832582058005)
                  ·
                    refine ⟨149729931889820277283969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3194238546982832582058005 149729931889820277283969)
                    ·
                      rfl

theorem cell22_437397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_437397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_437397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_437397 prefixEnd_437397 := by exact prefixLift 437397
  have htrace : WordTrace (prefixWord ++ tailWord_437397) baseStart_437397 baseEnd_437397 := by
    simpa [prefixWord, tailWord_437397, baseEnd_437397] using wordTrace_append hprefix tailTrace_437397
  have hstable : (prefixWord ++ tailWord_437397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437397).length < 2 ^ (prefixWord ++ tailWord_437397).sum := by decide
  have hdescent : baseEnd_437397 < baseStart_437397 := by decide
  rcases family_descends (prefixWord ++ tailWord_437397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437457 : List Nat := [1, 2, 2, 1, 2, 2, 1, 2, 9]
def baseStart_437457 : Nat := 118140960795 + 437457 * 2 ^ 59
def prefixEnd_437457 : Nat := 4983230072969 + 3 ^ 40 * 437457 * 2
def baseEnd_437457 : Nat := 49916823705333373594595

theorem tailTrace_437457 : CollatzResearch.WordTrace tailWord_437457 prefixEnd_437457 49916823705333373594595 := by
  unfold tailWord_437457
  simp only [CollatzResearch.WordTrace]
  refine ⟨15955367576175475552606625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10636911717450317035071083 15955367576175475552606625)
  ·
    refine ⟨11966525682131606664454969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15955367576175475552606625 11966525682131606664454969)
    ·
      refine ⟨8974894261598704998341227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11966525682131606664454969 8974894261598704998341227)
      ·
        refine ⟨13462341392398057497511841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8974894261598704998341227 13462341392398057497511841)
        ·
          refine ⟨10096756044298543123133881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13462341392398057497511841 10096756044298543123133881)
          ·
            refine ⟨7572567033223907342350411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10096756044298543123133881 7572567033223907342350411)
            ·
              refine ⟨11358850549835861013525617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7572567033223907342350411 11358850549835861013525617)
              ·
                refine ⟨8519137912376895760144213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11358850549835861013525617 8519137912376895760144213)
                ·
                  refine ⟨49916823705333373594595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 8519137912376895760144213 49916823705333373594595)
                  ·
                    rfl

theorem cell22_437457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 9].length) (baseStart_437457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_437457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_437457 prefixEnd_437457 := by exact prefixLift 437457
  have htrace : WordTrace (prefixWord ++ tailWord_437457) baseStart_437457 baseEnd_437457 := by
    simpa [prefixWord, tailWord_437457, baseEnd_437457] using wordTrace_append hprefix tailTrace_437457
  have hstable : (prefixWord ++ tailWord_437457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437457).length < 2 ^ (prefixWord ++ tailWord_437457).sum := by decide
  have hdescent : baseEnd_437457 < baseStart_437457 := by decide
  rcases family_descends (prefixWord ++ tailWord_437457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437461 : List Nat := [1, 3, 2, 4, 1, 1, 1, 1, 5, 3]
def baseStart_437461 : Nat := 118140960795 + 437461 * 2 ^ 59
def prefixEnd_437461 : Nat := 4983230072969 + 3 ^ 40 * 437461 * 2
def baseEnd_437461 : Nat := 149751840397745443683773

theorem tailTrace_437461 : CollatzResearch.WordTrace tailWord_437461 prefixEnd_437461 149751840397745443683773 := by
  unfold tailWord_437461
  simp only [CollatzResearch.WordTrace]
  refine ⟨15955513468160984235752237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10637008978773989490501491 15955513468160984235752237)
  ·
    refine ⟨5983317550560369088407089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15955513468160984235752237 5983317550560369088407089)
    ·
      refine ⟨4487488162920276816305317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5983317550560369088407089 4487488162920276816305317)
      ·
        refine ⟨841404030547551903057247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4487488162920276816305317 841404030547551903057247)
        ·
          refine ⟨1262106045821327854585871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 841404030547551903057247 1262106045821327854585871)
          ·
            refine ⟨1893159068731991781878807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1262106045821327854585871 1893159068731991781878807)
            ·
              refine ⟨2839738603097987672818211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1893159068731991781878807 2839738603097987672818211)
              ·
                refine ⟨4259607904646981509227317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2839738603097987672818211 4259607904646981509227317)
                ·
                  refine ⟨399338241060654516490061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4259607904646981509227317 399338241060654516490061)
                  ·
                    refine ⟨149751840397745443683773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 399338241060654516490061 149751840397745443683773)
                    ·
                      rfl

theorem cell22_437461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 5, 3].length) (baseStart_437461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_437461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_437461 prefixEnd_437461 := by exact prefixLift 437461
  have htrace : WordTrace (prefixWord ++ tailWord_437461) baseStart_437461 baseEnd_437461 := by
    simpa [prefixWord, tailWord_437461, baseEnd_437461] using wordTrace_append hprefix tailTrace_437461
  have hstable : (prefixWord ++ tailWord_437461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437461).length < 2 ^ (prefixWord ++ tailWord_437461).sum := by decide
  have hdescent : baseEnd_437461 < baseStart_437461 := by decide
  rcases family_descends (prefixWord ++ tailWord_437461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437491 : List Nat := [1, 1, 1, 2, 2, 7, 1, 2, 5]
def baseStart_437491 : Nat := 118140960795 + 437491 * 2 ^ 59
def prefixEnd_437491 : Nat := 4983230072969 + 3 ^ 40 * 437491 * 2
def baseEnd_437491 : Nat := 49920703336945121811227

theorem tailTrace_437491 : CollatzResearch.WordTrace tailWord_437491 prefixEnd_437491 49920703336945121811227 := by
  unfold tailWord_437491
  simp only [CollatzResearch.WordTrace]
  refine ⟨15956607658052299359344327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10637738438701532906229551 15956607658052299359344327)
  ·
    refine ⟨23934911487078449039016491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15956607658052299359344327 23934911487078449039016491)
    ·
      refine ⟨35902367230617673558524737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23934911487078449039016491 35902367230617673558524737)
      ·
        refine ⟨26926775422963255168893553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35902367230617673558524737 26926775422963255168893553)
        ·
          refine ⟨20195081567222441376670165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26926775422963255168893553 20195081567222441376670165)
          ·
            refine ⟨473322224231775969765707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 20195081567222441376670165 473322224231775969765707)
            ·
              refine ⟨709983336347663954648561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 473322224231775969765707 709983336347663954648561)
              ·
                refine ⟨532487502260747965986421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 709983336347663954648561 532487502260747965986421)
                ·
                  refine ⟨49920703336945121811227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 532487502260747965986421 49920703336945121811227)
                  ·
                    rfl

theorem cell22_437491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 2, 5].length) (baseStart_437491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_437491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_437491 prefixEnd_437491 := by exact prefixLift 437491
  have htrace : WordTrace (prefixWord ++ tailWord_437491) baseStart_437491 baseEnd_437491 := by
    simpa [prefixWord, tailWord_437491, baseEnd_437491] using wordTrace_append hprefix tailTrace_437491
  have hstable : (prefixWord ++ tailWord_437491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437491).length < 2 ^ (prefixWord ++ tailWord_437491).sum := by decide
  have hdescent : baseEnd_437491 < baseStart_437491 := by decide
  rcases family_descends (prefixWord ++ tailWord_437491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437508 : List Nat := [2, 3, 2, 2, 2, 2, 3, 1, 5]
def baseStart_437508 : Nat := 118140960795 + 437508 * 2 ^ 59
def prefixEnd_437508 : Nat := 4983230072969 + 3 ^ 40 * 437508 * 2
def baseEnd_437508 : Nat := 49922643152750995919543

theorem tailTrace_437508 : CollatzResearch.WordTrace tailWord_437508 prefixEnd_437508 49922643152750995919543 := by
  unfold tailWord_437508
  simp only [CollatzResearch.WordTrace]
  refine ⟨7978613849495355631356589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10638151799327140841808785 7978613849495355631356589)
  ·
    refine ⟨2991980193560758361758721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7978613849495355631356589 2991980193560758361758721)
    ·
      refine ⟨2243985145170568771319041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2991980193560758361758721 2243985145170568771319041)
      ·
        refine ⟨1682988858877926578489281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2243985145170568771319041 1682988858877926578489281)
        ·
          refine ⟨1262241644158444933866961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1682988858877926578489281 1262241644158444933866961)
          ·
            refine ⟨946681233118833700400221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1262241644158444933866961 946681233118833700400221)
            ·
              refine ⟨355005462419562637650083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 946681233118833700400221 355005462419562637650083)
              ·
                refine ⟨532508193629343956475125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 355005462419562637650083 532508193629343956475125)
                ·
                  refine ⟨49922643152750995919543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 532508193629343956475125 49922643152750995919543)
                  ·
                    rfl

theorem cell22_437508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3, 1, 5].length) (baseStart_437508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_437508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_437508 prefixEnd_437508 := by exact prefixLift 437508
  have htrace : WordTrace (prefixWord ++ tailWord_437508) baseStart_437508 baseEnd_437508 := by
    simpa [prefixWord, tailWord_437508, baseEnd_437508] using wordTrace_append hprefix tailTrace_437508
  have hstable : (prefixWord ++ tailWord_437508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437508).length < 2 ^ (prefixWord ++ tailWord_437508).sum := by decide
  have hdescent : baseEnd_437508 < baseStart_437508 := by decide
  rcases family_descends (prefixWord ++ tailWord_437508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437521 : List Nat := [1, 2, 2, 1, 1, 4, 4, 2, 1, 4]
def baseStart_437521 : Nat := 118140960795 + 437521 * 2 ^ 59
def prefixEnd_437521 : Nat := 4983230072969 + 3 ^ 40 * 437521 * 2
def baseEnd_437521 : Nat := 149772379623925287183589

theorem tailTrace_437521 : CollatzResearch.WordTrace tailWord_437521 prefixEnd_437521 149772379623925287183589 := by
  unfold tailWord_437521
  simp only [CollatzResearch.WordTrace]
  refine ⟨15957701847943614482936417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10638467898629076321957611 15957701847943614482936417)
  ·
    refine ⟨11968276385957710862202313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15957701847943614482936417 11968276385957710862202313)
    ·
      refine ⟨8976207289468283146651735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11968276385957710862202313 8976207289468283146651735)
      ·
        refine ⟨13464310934202424719977603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8976207289468283146651735 13464310934202424719977603)
        ·
          refine ⟨20196466401303637079966405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13464310934202424719977603 20196466401303637079966405)
          ·
            refine ⟨3786837450244431952493701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20196466401303637079966405 3786837450244431952493701)
            ·
              refine ⟨710032021920830991092569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3786837450244431952493701 710032021920830991092569)
              ·
                refine ⟨532524016440623243319427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 710032021920830991092569 532524016440623243319427)
                ·
                  refine ⟨798786024660934864979141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 532524016440623243319427 798786024660934864979141)
                  ·
                    refine ⟨149772379623925287183589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 798786024660934864979141 149772379623925287183589)
                    ·
                      rfl

theorem cell22_437521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 4].length) (baseStart_437521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_437521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_437521 prefixEnd_437521 := by exact prefixLift 437521
  have htrace : WordTrace (prefixWord ++ tailWord_437521) baseStart_437521 baseEnd_437521 := by
    simpa [prefixWord, tailWord_437521, baseEnd_437521] using wordTrace_append hprefix tailTrace_437521
  have hstable : (prefixWord ++ tailWord_437521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437521).length < 2 ^ (prefixWord ++ tailWord_437521).sum := by decide
  have hdescent : baseEnd_437521 < baseStart_437521 := by decide
  rcases family_descends (prefixWord ++ tailWord_437521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437551 : List Nat := [1, 1, 2, 1, 2, 1, 3, 6, 2, 3]
def baseStart_437551 : Nat := 118140960795 + 437551 * 2 ^ 59
def prefixEnd_437551 : Nat := 4983230072969 + 3 ^ 40 * 437551 * 2
def baseEnd_437551 : Nat := 149782649237015208933497

theorem tailTrace_437551 : CollatzResearch.WordTrace tailWord_437551 prefixEnd_437551 149782649237015208933497 := by
  unfold tailWord_437551
  simp only [CollatzResearch.WordTrace]
  refine ⟨15958796037834929606528507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10639197358556619737685671 15958796037834929606528507)
  ·
    refine ⟨23938194056752394409792761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15958796037834929606528507 23938194056752394409792761)
    ·
      refine ⟨17953645542564295807344571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23938194056752394409792761 17953645542564295807344571)
      ·
        refine ⟨26930468313846443711016857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17953645542564295807344571 26930468313846443711016857)
        ·
          refine ⟨20197851235384832783262643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26930468313846443711016857 20197851235384832783262643)
          ·
            refine ⟨30296776853077249174893965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20197851235384832783262643 30296776853077249174893965)
            ·
              refine ⟨11361291319903968440585237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30296776853077249174893965 11361291319903968440585237)
              ·
                refine ⟨532560530620498520652433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11361291319903968440585237 532560530620498520652433)
                ·
                  refine ⟨399420397965373890489325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 532560530620498520652433 399420397965373890489325)
                  ·
                    refine ⟨149782649237015208933497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 399420397965373890489325 149782649237015208933497)
                    ·
                      rfl

theorem cell22_437551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 6, 2, 3].length) (baseStart_437551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_437551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_437551 prefixEnd_437551 := by exact prefixLift 437551
  have htrace : WordTrace (prefixWord ++ tailWord_437551) baseStart_437551 baseEnd_437551 := by
    simpa [prefixWord, tailWord_437551, baseEnd_437551] using wordTrace_append hprefix tailTrace_437551
  have hstable : (prefixWord ++ tailWord_437551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437551).length < 2 ^ (prefixWord ++ tailWord_437551).sum := by decide
  have hdescent : baseEnd_437551 < baseStart_437551 := by decide
  rcases family_descends (prefixWord ++ tailWord_437551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437564 : List Nat := [2, 2, 2, 2, 1, 3, 1, 9]
def baseStart_437564 : Nat := 118140960795 + 437564 * 2 ^ 59
def prefixEnd_437564 : Nat := 4983230072969 + 3 ^ 40 * 437564 * 2
def baseEnd_437564 : Nat := 16643011044743056484273

theorem tailTrace_437564 : CollatzResearch.WordTrace tailWord_437564 prefixEnd_437564 16643011044743056484273 := by
  unfold tailWord_437564
  simp only [CollatzResearch.WordTrace]
  refine ⟨7979635093393916413375873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10639513457858555217834497 7979635093393916413375873)
  ·
    refine ⟨5984726320045437310031905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7979635093393916413375873 5984726320045437310031905)
    ·
      refine ⟨4488544740034077982523929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5984726320045437310031905 4488544740034077982523929)
      ·
        refine ⟨3366408555025558486892947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4488544740034077982523929 3366408555025558486892947)
        ·
          refine ⟨5049612832538337730339421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3366408555025558486892947 5049612832538337730339421)
          ·
            refine ⟨1893604812201876648877283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5049612832538337730339421 1893604812201876648877283)
            ·
              refine ⟨2840407218302814973315925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1893604812201876648877283 2840407218302814973315925)
              ·
                refine ⟨16643011044743056484273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2840407218302814973315925 16643011044743056484273)
                ·
                  rfl

theorem cell22_437564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 9].length) (baseStart_437564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_437564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_437564 prefixEnd_437564 := by exact prefixLift 437564
  have htrace : WordTrace (prefixWord ++ tailWord_437564) baseStart_437564 baseEnd_437564 := by
    simpa [prefixWord, tailWord_437564, baseEnd_437564] using wordTrace_append hprefix tailTrace_437564
  have hstable : (prefixWord ++ tailWord_437564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437564).length < 2 ^ (prefixWord ++ tailWord_437564).sum := by decide
  have hdescent : baseEnd_437564 < baseStart_437564 := by decide
  rcases family_descends (prefixWord ++ tailWord_437564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437566 : List Nat := [4, 2, 1, 2, 1, 1, 1, 2, 4, 4]
def baseStart_437566 : Nat := 118140960795 + 437566 * 2 ^ 59
def prefixEnd_437566 : Nat := 4983230072969 + 3 ^ 40 * 437566 * 2
def baseEnd_437566 : Nat := 149787784043560169808451

theorem tailTrace_437566 : CollatzResearch.WordTrace tailWord_437566 prefixEnd_437566 149787784043560169808451 := by
  unfold tailWord_437566
  simp only [CollatzResearch.WordTrace]
  refine ⟨1994917891597573396040569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10639562088520391445549701 1994917891597573396040569)
  ·
    refine ⟨1496188418698180047030427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1994917891597573396040569 1496188418698180047030427)
    ·
      refine ⟨2244282628047270070545641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1496188418698180047030427 2244282628047270070545641)
      ·
        refine ⟨1683211971035452552909231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2244282628047270070545641 1683211971035452552909231)
        ·
          refine ⟨2524817956553178829363847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1683211971035452552909231 2524817956553178829363847)
          ·
            refine ⟨3787226934829768244045771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2524817956553178829363847 3787226934829768244045771)
            ·
              refine ⟨5680840402244652366068657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3787226934829768244045771 5680840402244652366068657)
              ·
                refine ⟨4260630301683489274551493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5680840402244652366068657 4260630301683489274551493)
                ·
                  refine ⟨798868181565654238978405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4260630301683489274551493 798868181565654238978405)
                  ·
                    refine ⟨149787784043560169808451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 798868181565654238978405 149787784043560169808451)
                    ·
                      rfl

theorem cell22_437566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_437566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_437566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_437566 prefixEnd_437566 := by exact prefixLift 437566
  have htrace : WordTrace (prefixWord ++ tailWord_437566) baseStart_437566 baseEnd_437566 := by
    simpa [prefixWord, tailWord_437566, baseEnd_437566] using wordTrace_append hprefix tailTrace_437566
  have hstable : (prefixWord ++ tailWord_437566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437566).length < 2 ^ (prefixWord ++ tailWord_437566).sum := by decide
  have hdescent : baseEnd_437566 < baseStart_437566 := by decide
  rcases family_descends (prefixWord ++ tailWord_437566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437598 : List Nat := [4, 4, 2, 12]
def baseStart_437598 : Nat := 118140960795 + 437598 * 2 ^ 59
def prefixEnd_437598 : Nat := 4983230072969 + 3 ^ 40 * 437598 * 2
def baseEnd_437598 : Nat := 205485237719509949257

theorem tailTrace_437598 : CollatzResearch.WordTrace tailWord_437598 prefixEnd_437598 205485237719509949257 := by
  unfold tailWord_437598
  simp only [CollatzResearch.WordTrace]
  refine ⟨1995063783583082079186181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10640340179109771088992965 1995063783583082079186181)
  ·
    refine ⟨374074459421827889847409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1995063783583082079186181 374074459421827889847409)
    ·
      refine ⟨280555844566370917385557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 374074459421827889847409 280555844566370917385557)
      ·
        refine ⟨205485237719509949257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 280555844566370917385557 205485237719509949257)
        ·
          rfl

theorem cell22_437598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 12].length) (baseStart_437598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_437598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_437598 prefixEnd_437598 := by exact prefixLift 437598
  have htrace : WordTrace (prefixWord ++ tailWord_437598) baseStart_437598 baseEnd_437598 := by
    simpa [prefixWord, tailWord_437598, baseEnd_437598] using wordTrace_append hprefix tailTrace_437598
  have hstable : (prefixWord ++ tailWord_437598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437598).length < 2 ^ (prefixWord ++ tailWord_437598).sum := by decide
  have hdescent : baseEnd_437598 < baseStart_437598 := by decide
  rcases family_descends (prefixWord ++ tailWord_437598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437733 : List Nat := [1, 3, 1, 5, 1, 2, 2, 7]
def baseStart_437733 : Nat := 118140960795 + 437733 * 2 ^ 59
def prefixEnd_437733 : Nat := 4983230072969 + 3 ^ 40 * 437733 * 2
def baseEnd_437733 : Nat := 16649439061825266764771

theorem tailTrace_437733 : CollatzResearch.WordTrace tailWord_437733 prefixEnd_437733 16649439061825266764771 := by
  unfold tailWord_437733
  simp only [CollatzResearch.WordTrace]
  refine ⟨15965434123175574689653853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10643622748783716459769235 15965434123175574689653853)
  ·
    refine ⟨5987037796190840508620195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15965434123175574689653853 5987037796190840508620195)
    ·
      refine ⟨8980556694286260762930293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5987037796190840508620195 8980556694286260762930293)
      ·
        refine ⟨841927190089336946524715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8980556694286260762930293 841927190089336946524715)
        ·
          refine ⟨1262890785134005419787073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 841927190089336946524715 1262890785134005419787073)
          ·
            refine ⟨947168088850504064840305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1262890785134005419787073 947168088850504064840305)
            ·
              refine ⟨710376066637878048630229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 947168088850504064840305 710376066637878048630229)
              ·
                refine ⟨16649439061825266764771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 710376066637878048630229 16649439061825266764771)
                ·
                  rfl

theorem cell22_437733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 7].length) (baseStart_437733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_437733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_437733 prefixEnd_437733 := by exact prefixLift 437733
  have htrace : WordTrace (prefixWord ++ tailWord_437733) baseStart_437733 baseEnd_437733 := by
    simpa [prefixWord, tailWord_437733, baseEnd_437733] using wordTrace_append hprefix tailTrace_437733
  have hstable : (prefixWord ++ tailWord_437733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437733).length < 2 ^ (prefixWord ++ tailWord_437733).sum := by decide
  have hdescent : baseEnd_437733 < baseStart_437733 := by decide
  rcases family_descends (prefixWord ++ tailWord_437733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437765 : List Nat := [1, 3, 1, 1, 2, 2, 1, 7, 1, 3]
def baseStart_437765 : Nat := 118140960795 + 437765 * 2 ^ 59
def prefixEnd_437765 : Nat := 4983230072969 + 3 ^ 40 * 437765 * 2
def baseEnd_437765 : Nat := 149855905810389984082841

theorem tailTrace_437765 : CollatzResearch.WordTrace tailWord_437765 prefixEnd_437765 149855905810389984082841 := by
  unfold tailWord_437765
  simp only [CollatzResearch.WordTrace]
  refine ⟨15966601259059644154818749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10644400839373096103212499 15966601259059644154818749)
  ·
    refine ⟨5987475472147366558057031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15966601259059644154818749 5987475472147366558057031)
    ·
      refine ⟨8981213208221049837085547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5987475472147366558057031 8981213208221049837085547)
      ·
        refine ⟨13471819812331574755628321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8981213208221049837085547 13471819812331574755628321)
        ·
          refine ⟨10103864859248681066721241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13471819812331574755628321 10103864859248681066721241)
          ·
            refine ⟨7577898644436510800040931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10103864859248681066721241 7577898644436510800040931)
            ·
              refine ⟨11366847966654766200061397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7577898644436510800040931 11366847966654766200061397)
              ·
                refine ⟨266410499218471082813939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 11366847966654766200061397 266410499218471082813939)
                ·
                  refine ⟨399615748827706624220909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 266410499218471082813939 399615748827706624220909)
                  ·
                    refine ⟨149855905810389984082841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 399615748827706624220909 149855905810389984082841)
                    ·
                      rfl

theorem cell22_437765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 7, 1, 3].length) (baseStart_437765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_437765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_437765 prefixEnd_437765 := by exact prefixLift 437765
  have htrace : WordTrace (prefixWord ++ tailWord_437765) baseStart_437765 baseEnd_437765 := by
    simpa [prefixWord, tailWord_437765, baseEnd_437765] using wordTrace_append hprefix tailTrace_437765
  have hstable : (prefixWord ++ tailWord_437765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437765).length < 2 ^ (prefixWord ++ tailWord_437765).sum := by decide
  have hdescent : baseEnd_437765 < baseStart_437765 := by decide
  rcases family_descends (prefixWord ++ tailWord_437765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437773 : List Nat := [1, 7, 1, 1, 3, 1, 2, 2, 4]
def baseStart_437773 : Nat := 118140960795 + 437773 * 2 ^ 59
def prefixEnd_437773 : Nat := 4983230072969 + 3 ^ 40 * 437773 * 2
def baseEnd_437773 : Nat := 49952881457960209960939

theorem tailTrace_437773 : CollatzResearch.WordTrace tailWord_437773 prefixEnd_437773 49952881457960209960939 := by
  unfold tailWord_437773
  simp only [CollatzResearch.WordTrace]
  refine ⟨15966893043030661521109973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10644595362020441014073315 15966893043030661521109973)
  ·
    refine ⟨374224055696031129401015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 15966893043030661521109973 374224055696031129401015)
    ·
      refine ⟨561336083544046694101523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374224055696031129401015 561336083544046694101523)
      ·
        refine ⟨842004125316070041152285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 561336083544046694101523 842004125316070041152285)
        ·
          refine ⟨315751546993526265432107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 842004125316070041152285 315751546993526265432107)
          ·
            refine ⟨473627320490289398148161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315751546993526265432107 473627320490289398148161)
            ·
              refine ⟨355220490367717048611121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 473627320490289398148161 355220490367717048611121)
              ·
                refine ⟨266415367775787786458341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 355220490367717048611121 266415367775787786458341)
                ·
                  refine ⟨49952881457960209960939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 266415367775787786458341 49952881457960209960939)
                  ·
                    rfl

theorem cell22_437773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_437773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_437773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_437773 prefixEnd_437773 := by exact prefixLift 437773
  have htrace : WordTrace (prefixWord ++ tailWord_437773) baseStart_437773 baseEnd_437773 := by
    simpa [prefixWord, tailWord_437773, baseEnd_437773] using wordTrace_append hprefix tailTrace_437773
  have hstable : (prefixWord ++ tailWord_437773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437773).length < 2 ^ (prefixWord ++ tailWord_437773).sum := by decide
  have hdescent : baseEnd_437773 < baseStart_437773 := by decide
  rcases family_descends (prefixWord ++ tailWord_437773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437793 : List Nat := [1, 2, 3, 2, 2, 3, 1, 1, 2, 5]
def baseStart_437793 : Nat := 118140960795 + 437793 * 2 ^ 59
def prefixEnd_437793 : Nat := 4983230072969 + 3 ^ 40 * 437793 * 2
def baseEnd_437793 : Nat := 149865490782607244382755

theorem tailTrace_437793 : CollatzResearch.WordTrace tailWord_437793 prefixEnd_437793 149865490782607244382755 := by
  unfold tailWord_437793
  simp only [CollatzResearch.WordTrace]
  refine ⟨15967622502958204936838033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10645081668638803291225355 15967622502958204936838033)
  ·
    refine ⟨11975716877218653702628525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15967622502958204936838033 11975716877218653702628525)
    ·
      refine ⟨4490893828956995138485697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11975716877218653702628525 4490893828956995138485697)
      ·
        refine ⟨3368170371717746353864273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4490893828956995138485697 3368170371717746353864273)
        ·
          refine ⟨2526127778788309765398205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3368170371717746353864273 2526127778788309765398205)
          ·
            refine ⟨947297917045616162024327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2526127778788309765398205 947297917045616162024327)
            ·
              refine ⟨1420946875568424243036491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 947297917045616162024327 1420946875568424243036491)
              ·
                refine ⟨2131420313352636364554737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1420946875568424243036491 2131420313352636364554737)
                ·
                  refine ⟨1598565235014477273416053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2131420313352636364554737 1598565235014477273416053)
                  ·
                    refine ⟨149865490782607244382755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1598565235014477273416053 149865490782607244382755)
                    ·
                      rfl

theorem cell22_437793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_437793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_437793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_437793 prefixEnd_437793 := by exact prefixLift 437793
  have htrace : WordTrace (prefixWord ++ tailWord_437793) baseStart_437793 baseEnd_437793 := by
    simpa [prefixWord, tailWord_437793, baseEnd_437793] using wordTrace_append hprefix tailTrace_437793
  have hstable : (prefixWord ++ tailWord_437793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437793).length < 2 ^ (prefixWord ++ tailWord_437793).sum := by decide
  have hdescent : baseEnd_437793 < baseStart_437793 := by decide
  rcases family_descends (prefixWord ++ tailWord_437793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437808 : List Nat := [2, 1, 1, 1, 2, 3, 1, 6, 1, 4]
def baseStart_437808 : Nat := 118140960795 + 437808 * 2 ^ 59
def prefixEnd_437808 : Nat := 4983230072969 + 3 ^ 40 * 437808 * 2
def baseEnd_437808 : Nat := 149870625589152205257709

theorem tailTrace_437808 : CollatzResearch.WordTrace tailWord_437808 prefixEnd_437808 149870625589152205257709 := by
  unfold tailWord_437808
  simp only [CollatzResearch.WordTrace]
  refine ⟨7984084798951931249317039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10645446398602574999089385 7984084798951931249317039)
  ·
    refine ⟨11976127198427896873975559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7984084798951931249317039 11976127198427896873975559)
    ·
      refine ⟨17964190797641845310963339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11976127198427896873975559 17964190797641845310963339)
      ·
        refine ⟨26946286196462767966445009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17964190797641845310963339 26946286196462767966445009)
        ·
          refine ⟨20209714647347075974833757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26946286196462767966445009 20209714647347075974833757)
          ·
            refine ⟨7578642992755153490562659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20209714647347075974833757 7578642992755153490562659)
            ·
              refine ⟨11367964489132730235843989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7578642992755153490562659 11367964489132730235843989)
              ·
                refine ⟨532873335428096729805187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11367964489132730235843989 532873335428096729805187)
                ·
                  refine ⟨799310003142145094707781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 532873335428096729805187 799310003142145094707781)
                  ·
                    refine ⟨149870625589152205257709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 799310003142145094707781 149870625589152205257709)
                    ·
                      rfl

theorem cell22_437808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 6, 1, 4].length) (baseStart_437808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_437808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_437808 prefixEnd_437808 := by exact prefixLift 437808
  have htrace : WordTrace (prefixWord ++ tailWord_437808) baseStart_437808 baseEnd_437808 := by
    simpa [prefixWord, tailWord_437808, baseEnd_437808] using wordTrace_append hprefix tailTrace_437808
  have hstable : (prefixWord ++ tailWord_437808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437808).length < 2 ^ (prefixWord ++ tailWord_437808).sum := by decide
  have hdescent : baseEnd_437808 < baseStart_437808 := by decide
  rcases family_descends (prefixWord ++ tailWord_437808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437825 : List Nat := [1, 2, 5, 1, 1, 1, 3, 3, 1, 4]
def baseStart_437825 : Nat := 118140960795 + 437825 * 2 ^ 59
def prefixEnd_437825 : Nat := 4983230072969 + 3 ^ 40 * 437825 * 2
def baseEnd_437825 : Nat := 149876445036569827582657

theorem tailTrace_437825 : CollatzResearch.WordTrace tailWord_437825 prefixEnd_437825 149876445036569827582657 := by
  unfold tailWord_437825
  simp only [CollatzResearch.WordTrace]
  refine ⟨15968789638842274402002929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10645859759228182934668619 15968789638842274402002929)
  ·
    refine ⟨11976592229131705801502197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15968789638842274402002929 11976592229131705801502197)
    ·
      refine ⟨1122805521481097418890831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11976592229131705801502197 1122805521481097418890831)
      ·
        refine ⟨1684208282221646128336247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1122805521481097418890831 1684208282221646128336247)
        ·
          refine ⟨2526312423332469192504371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1684208282221646128336247 2526312423332469192504371)
          ·
            refine ⟨3789468634998703788756557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2526312423332469192504371 3789468634998703788756557)
            ·
              refine ⟨1421050738124513920783709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3789468634998703788756557 1421050738124513920783709)
              ·
                refine ⟨532894026796692720293891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1421050738124513920783709 532894026796692720293891)
                ·
                  refine ⟨799341040195039080440837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 532894026796692720293891 799341040195039080440837)
                  ·
                    refine ⟨149876445036569827582657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 799341040195039080440837 149876445036569827582657)
                    ·
                      rfl

theorem cell22_437825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_437825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_437825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_437825 prefixEnd_437825 := by exact prefixLift 437825
  have htrace : WordTrace (prefixWord ++ tailWord_437825) baseStart_437825 baseEnd_437825 := by
    simpa [prefixWord, tailWord_437825, baseEnd_437825] using wordTrace_append hprefix tailTrace_437825
  have hstable : (prefixWord ++ tailWord_437825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437825).length < 2 ^ (prefixWord ++ tailWord_437825).sum := by decide
  have hdescent : baseEnd_437825 < baseStart_437825 := by decide
  rcases family_descends (prefixWord ++ tailWord_437825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437846 : List Nat := [5, 2, 2, 2, 1, 1, 3, 1, 5]
def baseStart_437846 : Nat := 118140960795 + 437846 * 2 ^ 59
def prefixEnd_437846 : Nat := 4983230072969 + 3 ^ 40 * 437846 * 2
def baseEnd_437846 : Nat := 49961211255244257602531

theorem tailTrace_437846 : CollatzResearch.WordTrace tailWord_437846 prefixEnd_437846 49961211255244257602531 := by
  unfold tailWord_437846
  simp only [CollatzResearch.WordTrace]
  refine ⟨998097223235387186782337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10646370381177463325678261 998097223235387186782337)
  ·
    refine ⟨748572917426540390086753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 998097223235387186782337 748572917426540390086753)
    ·
      refine ⟨561429688069905292565065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 748572917426540390086753 561429688069905292565065)
      ·
        refine ⟨421072266052428969423799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 561429688069905292565065 421072266052428969423799)
        ·
          refine ⟨631608399078643454135699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 421072266052428969423799 631608399078643454135699)
          ·
            refine ⟨947412598617965181203549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 631608399078643454135699 947412598617965181203549)
            ·
              refine ⟨355279724481736942951331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 947412598617965181203549 355279724481736942951331)
              ·
                refine ⟨532919586722605414426997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 355279724481736942951331 532919586722605414426997)
                ·
                  refine ⟨49961211255244257602531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 532919586722605414426997 49961211255244257602531)
                  ·
                    rfl

theorem cell22_437846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_437846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_437846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_437846 prefixEnd_437846 := by exact prefixLift 437846
  have htrace : WordTrace (prefixWord ++ tailWord_437846) baseStart_437846 baseEnd_437846 := by
    simpa [prefixWord, tailWord_437846, baseEnd_437846] using wordTrace_append hprefix tailTrace_437846
  have hstable : (prefixWord ++ tailWord_437846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437846).length < 2 ^ (prefixWord ++ tailWord_437846).sum := by decide
  have hdescent : baseEnd_437846 < baseStart_437846 := by decide
  rcases family_descends (prefixWord ++ tailWord_437846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437906 : List Nat := [3, 2, 3, 1, 3, 2, 2, 1, 2, 3]
def baseStart_437906 : Nat := 118140960795 + 437906 * 2 ^ 59
def prefixEnd_437906 : Nat := 4983230072969 + 3 ^ 40 * 437906 * 2
def baseEnd_437906 : Nat := 149904172991912616307409

theorem tailTrace_437906 : CollatzResearch.WordTrace tailWord_437906 prefixEnd_437906 149904172991912616307409 := by
  unfold tailWord_437906
  simp only [CollatzResearch.WordTrace]
  refine ⟨3992935987887206308925393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10647829301032550157134381 3992935987887206308925393)
  ·
    refine ⟨2994701990915404731694045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3992935987887206308925393 2994701990915404731694045)
    ·
      refine ⟨1123013246593276774385267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2994701990915404731694045 1123013246593276774385267)
      ·
        refine ⟨1684519869889915161577901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1123013246593276774385267 1684519869889915161577901)
        ·
          refine ⟨631694951208718185591713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1684519869889915161577901 631694951208718185591713)
          ·
            refine ⟨473771213406538639193785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 631694951208718185591713 473771213406538639193785)
            ·
              refine ⟨355328410054903979395339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 473771213406538639193785 355328410054903979395339)
              ·
                refine ⟨532992615082355969093009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 355328410054903979395339 532992615082355969093009)
                ·
                  refine ⟨399744461311766976819757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 532992615082355969093009 399744461311766976819757)
                  ·
                    refine ⟨149904172991912616307409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 399744461311766976819757 149904172991912616307409)
                    ·
                      rfl

theorem cell22_437906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_437906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_437906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_437906 prefixEnd_437906 := by exact prefixLift 437906
  have htrace : WordTrace (prefixWord ++ tailWord_437906) baseStart_437906 baseEnd_437906 := by
    simpa [prefixWord, tailWord_437906, baseEnd_437906] using wordTrace_append hprefix tailTrace_437906
  have hstable : (prefixWord ++ tailWord_437906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437906).length < 2 ^ (prefixWord ++ tailWord_437906).sum := by decide
  have hdescent : baseEnd_437906 < baseStart_437906 := by decide
  rcases family_descends (prefixWord ++ tailWord_437906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437992 : List Nat := [2, 1, 4, 1, 3, 1, 1, 5, 4]
def baseStart_437992 : Nat := 118140960795 + 437992 * 2 ^ 59
def prefixEnd_437992 : Nat := 4983230072969 + 3 ^ 40 * 437992 * 2
def baseEnd_437992 : Nat := 49977870849812352885715

theorem tailTrace_437992 : CollatzResearch.WordTrace tailWord_437992 prefixEnd_437992 49977870849812352885715 := by
  unfold tailWord_437992
  simp only [CollatzResearch.WordTrace]
  refine ⟨7987440314618630961666115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10649920419491507948888153 7987440314618630961666115)
  ·
    refine ⟨11981160471927946442499173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7987440314618630961666115 11981160471927946442499173)
    ·
      refine ⟨2246467588486489957968595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11981160471927946442499173 2246467588486489957968595)
      ·
        refine ⟨3369701382729734936952893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2246467588486489957968595 3369701382729734936952893)
        ·
          refine ⟨1263638018523650601357335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3369701382729734936952893 1263638018523650601357335)
          ·
            refine ⟨1895457027785475902036003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1263638018523650601357335 1895457027785475902036003)
            ·
              refine ⟨2843185541678213853054005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1895457027785475902036003 2843185541678213853054005)
              ·
                refine ⟨266548644532332548723813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2843185541678213853054005 266548644532332548723813)
                ·
                  refine ⟨49977870849812352885715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 266548644532332548723813 49977870849812352885715)
                  ·
                    rfl

theorem cell22_437992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 5, 4].length) (baseStart_437992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_437992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_437992 prefixEnd_437992 := by exact prefixLift 437992
  have htrace : WordTrace (prefixWord ++ tailWord_437992) baseStart_437992 baseEnd_437992 := by
    simpa [prefixWord, tailWord_437992, baseEnd_437992] using wordTrace_append hprefix tailTrace_437992
  have hstable : (prefixWord ++ tailWord_437992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437992).length < 2 ^ (prefixWord ++ tailWord_437992).sum := by decide
  have hdescent : baseEnd_437992 < baseStart_437992 := by decide
  rcases family_descends (prefixWord ++ tailWord_437992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438007 : List Nat := [1, 1, 3, 1, 1, 1, 7, 2, 2, 3]
def baseStart_438007 : Nat := 118140960795 + 438007 * 2 ^ 59
def prefixEnd_438007 : Nat := 4983230072969 + 3 ^ 40 * 438007 * 2
def baseEnd_438007 : Nat := 149938747355982019532099

theorem tailTrace_438007 : CollatzResearch.WordTrace tailWord_438007 prefixEnd_438007 149938747355982019532099 := by
  unfold tailWord_438007
  simp only [CollatzResearch.WordTrace]
  refine ⟨15975427724182919485128275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10650285149455279656752183 15975427724182919485128275)
  ·
    refine ⟨23963141586274379227692413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15975427724182919485128275 23963141586274379227692413)
    ·
      refine ⟨8986178094852892210384655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23963141586274379227692413 8986178094852892210384655)
      ·
        refine ⟨13479267142279338315576983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8986178094852892210384655 13479267142279338315576983)
        ·
          refine ⟨20218900713419007473365475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13479267142279338315576983 20218900713419007473365475)
          ·
            refine ⟨30328351070128511210048213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20218900713419007473365475 30328351070128511210048213)
            ·
              refine ⟨710820728206136981485505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 30328351070128511210048213 710820728206136981485505)
              ·
                refine ⟨533115546154602736114129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 710820728206136981485505 533115546154602736114129)
                ·
                  refine ⟨399836659615952052085597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 533115546154602736114129 399836659615952052085597)
                  ·
                    refine ⟨149938747355982019532099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 399836659615952052085597 149938747355982019532099)
                    ·
                      rfl

theorem cell22_438007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 2, 2, 3].length) (baseStart_438007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_438007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_438007 prefixEnd_438007 := by exact prefixLift 438007
  have htrace : WordTrace (prefixWord ++ tailWord_438007) baseStart_438007 baseEnd_438007 := by
    simpa [prefixWord, tailWord_438007, baseEnd_438007] using wordTrace_append hprefix tailTrace_438007
  have hstable : (prefixWord ++ tailWord_438007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438007).length < 2 ^ (prefixWord ++ tailWord_438007).sum := by decide
  have hdescent : baseEnd_438007 < baseStart_438007 := by decide
  rcases family_descends (prefixWord ++ tailWord_438007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438024 : List Nat := [2, 1, 3, 2, 2, 1, 5, 1, 2, 3]
def baseStart_438024 : Nat := 118140960795 + 438024 * 2 ^ 59
def prefixEnd_438024 : Nat := 4983230072969 + 3 ^ 40 * 438024 * 2
def baseEnd_438024 : Nat := 149944566803399641857047

theorem tailTrace_438024 : CollatzResearch.WordTrace tailWord_438024 prefixEnd_438024 149944566803399641857047 := by
  unfold tailWord_438024
  simp only [CollatzResearch.WordTrace]
  refine ⟨7988023882560665694248563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10650698510080887592331417 7988023882560665694248563)
  ·
    refine ⟨11982035823840998541372845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7988023882560665694248563 11982035823840998541372845)
    ·
      refine ⟨4493263433940374453014817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11982035823840998541372845 4493263433940374453014817)
      ·
        refine ⟨3369947575455280839761113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4493263433940374453014817 3369947575455280839761113)
        ·
          refine ⟨2527460681591460629820835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3369947575455280839761113 2527460681591460629820835)
          ·
            refine ⟨3791191022387190944731253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2527460681591460629820835 3791191022387190944731253)
            ·
              refine ⟨355424158348799151068555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3791191022387190944731253 355424158348799151068555)
              ·
                refine ⟨533136237523198726602833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 355424158348799151068555 533136237523198726602833)
                ·
                  refine ⟨399852178142399044952125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 533136237523198726602833 399852178142399044952125)
                  ·
                    refine ⟨149944566803399641857047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 399852178142399044952125 149944566803399641857047)
                    ·
                      rfl

theorem cell22_438024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5, 1, 2, 3].length) (baseStart_438024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_438024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_438024 prefixEnd_438024 := by exact prefixLift 438024
  have htrace : WordTrace (prefixWord ++ tailWord_438024) baseStart_438024 baseEnd_438024 := by
    simpa [prefixWord, tailWord_438024, baseEnd_438024] using wordTrace_append hprefix tailTrace_438024
  have hstable : (prefixWord ++ tailWord_438024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438024).length < 2 ^ (prefixWord ++ tailWord_438024).sum := by decide
  have hdescent : baseEnd_438024 < baseStart_438024 := by decide
  rcases family_descends (prefixWord ++ tailWord_438024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438035 : List Nat := [1, 1, 1, 2, 1, 3, 2, 3, 5, 3]
def baseStart_438035 : Nat := 118140960795 + 438035 * 2 ^ 59
def prefixEnd_438035 : Nat := 4983230072969 + 3 ^ 40 * 438035 * 2
def baseEnd_438035 : Nat := 149948332328199279832013

theorem tailTrace_438035 : CollatzResearch.WordTrace tailWord_438035 prefixEnd_438035 149948332328199279832013 := by
  unfold tailWord_438035
  simp only [CollatzResearch.WordTrace]
  refine ⟨15976448968081480267147559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10650965978720986844765039 15976448968081480267147559)
  ·
    refine ⟨23964673452122220400721339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15976448968081480267147559 23964673452122220400721339)
    ·
      refine ⟨35947010178183330601082009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23964673452122220400721339 35947010178183330601082009)
      ·
        refine ⟨26960257633637497950811507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35947010178183330601082009 26960257633637497950811507)
        ·
          refine ⟨40440386450456246926217261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26960257633637497950811507 40440386450456246926217261)
          ·
            refine ⟨15165144918921092597331473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40440386450456246926217261 15165144918921092597331473)
            ·
              refine ⟨11373858689190819447998605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15165144918921092597331473 11373858689190819447998605)
              ·
                refine ⟨4265197008446557292999477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11373858689190819447998605 4265197008446557292999477)
                ·
                  refine ⟨399862219541864746218701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4265197008446557292999477 399862219541864746218701)
                  ·
                    refine ⟨149948332328199279832013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 399862219541864746218701 149948332328199279832013)
                    ·
                      rfl

theorem cell22_438035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 5, 3].length) (baseStart_438035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_438035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_438035 prefixEnd_438035 := by exact prefixLift 438035
  have htrace : WordTrace (prefixWord ++ tailWord_438035) baseStart_438035 baseEnd_438035 := by
    simpa [prefixWord, tailWord_438035, baseEnd_438035] using wordTrace_append hprefix tailTrace_438035
  have hstable : (prefixWord ++ tailWord_438035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438035).length < 2 ^ (prefixWord ++ tailWord_438035).sum := by decide
  have hdescent : baseEnd_438035 < baseStart_438035 := by decide
  rcases family_descends (prefixWord ++ tailWord_438035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438037 : List Nat := [1, 3, 2, 1, 2, 5, 2, 6]
def baseStart_438037 : Nat := 118140960795 + 438037 * 2 ^ 59
def prefixEnd_438037 : Nat := 4983230072969 + 3 ^ 40 * 438037 * 2
def baseEnd_438037 : Nat := 16661001885452437920223

theorem tailTrace_438037 : CollatzResearch.WordTrace tailWord_438037 prefixEnd_438037 16661001885452437920223 := by
  unfold tailWord_438037
  simp only [CollatzResearch.WordTrace]
  refine ⟨15976521914074234608720365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10651014609382823072480243 15976521914074234608720365)
  ·
    refine ⟨5991195717777837978270137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15976521914074234608720365 5991195717777837978270137)
    ·
      refine ⟨4493396788333378483702603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5991195717777837978270137 4493396788333378483702603)
      ·
        refine ⟨6740095182500067725553905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4493396788333378483702603 6740095182500067725553905)
        ·
          refine ⟨5055071386875050794165429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6740095182500067725553905 5055071386875050794165429)
          ·
            refine ⟨473912942519536011953009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5055071386875050794165429 473912942519536011953009)
            ·
              refine ⟨355434706889652008964757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 473912942519536011953009 355434706889652008964757)
              ·
                refine ⟨16661001885452437920223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 355434706889652008964757 16661001885452437920223)
                ·
                  rfl

theorem cell22_438037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2, 6].length) (baseStart_438037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_438037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_438037 prefixEnd_438037 := by exact prefixLift 438037
  have htrace : WordTrace (prefixWord ++ tailWord_438037) baseStart_438037 baseEnd_438037 := by
    simpa [prefixWord, tailWord_438037, baseEnd_438037] using wordTrace_append hprefix tailTrace_438037
  have hstable : (prefixWord ++ tailWord_438037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438037).length < 2 ^ (prefixWord ++ tailWord_438037).sum := by decide
  have hdescent : baseEnd_438037 < baseStart_438037 := by decide
  rcases family_descends (prefixWord ++ tailWord_438037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438065 : List Nat := [1, 2, 2, 3, 2, 2, 2, 1, 7]
def baseStart_438065 : Nat := 118140960795 + 438065 * 2 ^ 59
def prefixEnd_438065 : Nat := 4983230072969 + 3 ^ 40 * 438065 * 2
def baseEnd_438065 : Nat := 49986200647096400527307

theorem tailTrace_438065 : CollatzResearch.WordTrace tailWord_438065 prefixEnd_438065 49986200647096400527307 := by
  unfold tailWord_438065
  simp only [CollatzResearch.WordTrace]
  refine ⟨15977543157972795390739649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10651695438648530260493099 15977543157972795390739649)
  ·
    refine ⟨11983157368479596543054737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15977543157972795390739649 11983157368479596543054737)
    ·
      refine ⟨8987368026359697407291053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11983157368479596543054737 8987368026359697407291053)
      ·
        refine ⟨3370263009884886527734145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8987368026359697407291053 3370263009884886527734145)
        ·
          refine ⟨2527697257413664895800609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3370263009884886527734145 2527697257413664895800609)
          ·
            refine ⟨1895772943060248671850457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2527697257413664895800609 1895772943060248671850457)
            ·
              refine ⟨1421829707295186503887843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1895772943060248671850457 1421829707295186503887843)
              ·
                refine ⟨2132744560942779755831765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1421829707295186503887843 2132744560942779755831765)
                ·
                  refine ⟨49986200647096400527307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2132744560942779755831765 49986200647096400527307)
                  ·
                    rfl

theorem cell22_438065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 7].length) (baseStart_438065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_438065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_438065 prefixEnd_438065 := by exact prefixLift 438065
  have htrace : WordTrace (prefixWord ++ tailWord_438065) baseStart_438065 baseEnd_438065 := by
    simpa [prefixWord, tailWord_438065, baseEnd_438065] using wordTrace_append hprefix tailTrace_438065
  have hstable : (prefixWord ++ tailWord_438065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438065).length < 2 ^ (prefixWord ++ tailWord_438065).sum := by decide
  have hdescent : baseEnd_438065 < baseStart_438065 := by decide
  rcases family_descends (prefixWord ++ tailWord_438065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438172 : List Nat := [2, 2, 3, 3, 1, 2, 9]
def baseStart_438172 : Nat := 118140960795 + 438172 * 2 ^ 59
def prefixEnd_438172 : Nat := 4983230072969 + 3 ^ 40 * 438172 * 2
def baseEnd_438172 : Nat := 5555378897332466265059

theorem tailTrace_438172 : CollatzResearch.WordTrace tailWord_438172 prefixEnd_438172 5555378897332466265059 := by
  unfold tailWord_438172
  simp only [CollatzResearch.WordTrace]
  refine ⟨7990722884292576332442385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10654297179056768443256513 7990722884292576332442385)
  ·
    refine ⟨5993042163219432249331789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7990722884292576332442385 5993042163219432249331789)
    ·
      refine ⟨2247390811207287093499421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5993042163219432249331789 2247390811207287093499421)
      ·
        refine ⟨842771554202732660062283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2247390811207287093499421 842771554202732660062283)
        ·
          refine ⟨1264157331304098990093425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 842771554202732660062283 1264157331304098990093425)
          ·
            refine ⟨948117998478074242570069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1264157331304098990093425 948117998478074242570069)
            ·
              refine ⟨5555378897332466265059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 948117998478074242570069 5555378897332466265059)
              ·
                rfl

theorem cell22_438172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 9].length) (baseStart_438172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_438172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_438172 prefixEnd_438172 := by exact prefixLift 438172
  have htrace : WordTrace (prefixWord ++ tailWord_438172) baseStart_438172 baseEnd_438172 := by
    simpa [prefixWord, tailWord_438172, baseEnd_438172] using wordTrace_append hprefix tailTrace_438172
  have hstable : (prefixWord ++ tailWord_438172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438172).length < 2 ^ (prefixWord ++ tailWord_438172).sum := by decide
  have hdescent : baseEnd_438172 < baseStart_438172 := by decide
  rcases family_descends (prefixWord ++ tailWord_438172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438185 : List Nat := [1, 2, 1, 1, 1, 1, 4, 3, 2, 6]
def baseStart_438185 : Nat := 118140960795 + 438185 * 2 ^ 59
def prefixEnd_438185 : Nat := 4983230072969 + 3 ^ 40 * 438185 * 2
def baseEnd_438185 : Nat := 149999680393648888581553

theorem tailTrace_438185 : CollatzResearch.WordTrace tailWord_438185 prefixEnd_438185 149999680393648888581553 := by
  unfold tailWord_438185
  simp only [CollatzResearch.WordTrace]
  refine ⟨15981919917538055885108009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10654613278358703923405339 15981919917538055885108009)
  ·
    refine ⟨11986439938153541913831007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15981919917538055885108009 11986439938153541913831007)
    ·
      refine ⟨17979659907230312870746511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11986439938153541913831007 17979659907230312870746511)
      ·
        refine ⟨26969489860845469306119767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17979659907230312870746511 26969489860845469306119767)
        ·
          refine ⟨40454234791268203959179651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26969489860845469306119767 40454234791268203959179651)
          ·
            refine ⟨60681352186902305938769477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40454234791268203959179651 60681352186902305938769477)
            ·
              refine ⟨11377753535044182363519277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60681352186902305938769477 11377753535044182363519277)
              ·
                refine ⟨4266657575641568386319729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11377753535044182363519277 4266657575641568386319729)
                ·
                  refine ⟨3199993181731176289739797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4266657575641568386319729 3199993181731176289739797)
                  ·
                    refine ⟨149999680393648888581553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3199993181731176289739797 149999680393648888581553)
                    ·
                      rfl

theorem cell22_438185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 6].length) (baseStart_438185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_438185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_438185 prefixEnd_438185 := by exact prefixLift 438185
  have htrace : WordTrace (prefixWord ++ tailWord_438185) baseStart_438185 baseEnd_438185 := by
    simpa [prefixWord, tailWord_438185, baseEnd_438185] using wordTrace_append hprefix tailTrace_438185
  have hstable : (prefixWord ++ tailWord_438185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438185).length < 2 ^ (prefixWord ++ tailWord_438185).sum := by decide
  have hdescent : baseEnd_438185 < baseStart_438185 := by decide
  rcases family_descends (prefixWord ++ tailWord_438185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438264 : List Nat := [2, 1, 2, 1, 1, 3, 5, 2, 1, 4]
def baseStart_438264 : Nat := 118140960795 + 438264 * 2 ^ 59
def prefixEnd_438264 : Nat := 4983230072969 + 3 ^ 40 * 438264 * 2
def baseEnd_438264 : Nat := 150026723708119015856311

theorem tailTrace_438264 : CollatzResearch.WordTrace tailWord_438264 prefixEnd_438264 150026723708119015856311 := by
  unfold tailWord_438264
  simp only [CollatzResearch.WordTrace]
  refine ⟨7992400642125926188616923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10656534189501234918155897 7992400642125926188616923)
  ·
    refine ⟨11988600963188889282925385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7992400642125926188616923 11988600963188889282925385)
    ·
      refine ⟨8991450722391666962194039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11988600963188889282925385 8991450722391666962194039)
      ·
        refine ⟨13487176083587500443291059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8991450722391666962194039 13487176083587500443291059)
        ·
          refine ⟨20230764125381250664936589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13487176083587500443291059 20230764125381250664936589)
          ·
            refine ⟨7586536547017968999351221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20230764125381250664936589 7586536547017968999351221)
            ·
              refine ⟨711237801282934593689177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7586536547017968999351221 711237801282934593689177)
              ·
                refine ⟨533428350962200945266883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 711237801282934593689177 533428350962200945266883)
                ·
                  refine ⟨800142526443301417900325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 533428350962200945266883 800142526443301417900325)
                  ·
                    refine ⟨150026723708119015856311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 800142526443301417900325 150026723708119015856311)
                    ·
                      rfl

theorem cell22_438264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 2, 1, 4].length) (baseStart_438264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_438264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_438264 prefixEnd_438264 := by exact prefixLift 438264
  have htrace : WordTrace (prefixWord ++ tailWord_438264) baseStart_438264 baseEnd_438264 := by
    simpa [prefixWord, tailWord_438264, baseEnd_438264] using wordTrace_append hprefix tailTrace_438264
  have hstable : (prefixWord ++ tailWord_438264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438264).length < 2 ^ (prefixWord ++ tailWord_438264).sum := by decide
  have hdescent : baseEnd_438264 < baseStart_438264 := by decide
  rcases family_descends (prefixWord ++ tailWord_438264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438277 : List Nat := [1, 3, 1, 1, 2, 4, 1, 1, 3, 5]
def baseStart_438277 : Nat := 118140960795 + 438277 * 2 ^ 59
def prefixEnd_438277 : Nat := 4983230072969 + 3 ^ 40 * 438277 * 2
def baseEnd_438277 : Nat := 150031173873791315281271

theorem tailTrace_438277 : CollatzResearch.WordTrace tailWord_438277 prefixEnd_438277 150031173873791315281271 := by
  unfold tailWord_438277
  simp only [CollatzResearch.WordTrace]
  refine ⟨15985275433204755597457085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10656850288803170398304723 15985275433204755597457085)
  ·
    refine ⟨5994478287451783349046407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15985275433204755597457085 5994478287451783349046407)
    ·
      refine ⟨8991717431177675023569611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5994478287451783349046407 8991717431177675023569611)
      ·
        refine ⟨13487576146766512535354417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8991717431177675023569611 13487576146766512535354417)
        ·
          refine ⟨10115682110074884401515813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13487576146766512535354417 10115682110074884401515813)
          ·
            refine ⟨1896690395639040825284215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10115682110074884401515813 1896690395639040825284215)
            ·
              refine ⟨2845035593458561237926323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1896690395639040825284215 2845035593458561237926323)
              ·
                refine ⟨4267553390187841856889485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2845035593458561237926323 4267553390187841856889485)
                ·
                  refine ⟨1600332521320440696333557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4267553390187841856889485 1600332521320440696333557)
                  ·
                    refine ⟨150031173873791315281271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1600332521320440696333557 150031173873791315281271)
                    ·
                      rfl

theorem cell22_438277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 3, 5].length) (baseStart_438277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_438277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_438277 prefixEnd_438277 := by exact prefixLift 438277
  have htrace : WordTrace (prefixWord ++ tailWord_438277) baseStart_438277 baseEnd_438277 := by
    simpa [prefixWord, tailWord_438277, baseEnd_438277] using wordTrace_append hprefix tailTrace_438277
  have hstable : (prefixWord ++ tailWord_438277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438277).length < 2 ^ (prefixWord ++ tailWord_438277).sum := by decide
  have hdescent : baseEnd_438277 < baseStart_438277 := by decide
  rcases family_descends (prefixWord ++ tailWord_438277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438285 : List Nat := [1, 7, 1, 2, 1, 1, 2, 2, 5]
def baseStart_438285 : Nat := 118140960795 + 438285 * 2 ^ 59
def prefixEnd_438285 : Nat := 4983230072969 + 3 ^ 40 * 438285 * 2
def baseEnd_438285 : Nat := 50011304145760653693749

theorem tailTrace_438285 : CollatzResearch.WordTrace tailWord_438285 prefixEnd_438285 50011304145760653693749 := by
  unfold tailWord_438285
  simp only [CollatzResearch.WordTrace]
  refine ⟨15985567217175772963748309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10657044811450515309165539 15985567217175772963748309)
  ·
    refine ⟨374661731652557178837851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 15985567217175772963748309 374661731652557178837851)
    ·
      refine ⟨561992597478835768256777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374661731652557178837851 561992597478835768256777)
      ·
        refine ⟨421494448109126826192583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 561992597478835768256777 421494448109126826192583)
        ·
          refine ⟨632241672163690239288875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 421494448109126826192583 632241672163690239288875)
          ·
            refine ⟨948362508245535358933313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 632241672163690239288875 948362508245535358933313)
            ·
              refine ⟨711271881184151519199985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 948362508245535358933313 711271881184151519199985)
              ·
                refine ⟨533453910888113639399989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 711271881184151519199985 533453910888113639399989)
                ·
                  refine ⟨50011304145760653693749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 533453910888113639399989 50011304145760653693749)
                  ·
                    rfl

theorem cell22_438285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_438285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_438285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_438285 prefixEnd_438285 := by exact prefixLift 438285
  have htrace : WordTrace (prefixWord ++ tailWord_438285) baseStart_438285 baseEnd_438285 := by
    simpa [prefixWord, tailWord_438285, baseEnd_438285] using wordTrace_append hprefix tailTrace_438285
  have hstable : (prefixWord ++ tailWord_438285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438285).length < 2 ^ (prefixWord ++ tailWord_438285).sum := by decide
  have hdescent : baseEnd_438285 < baseStart_438285 := by decide
  rcases family_descends (prefixWord ++ tailWord_438285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438367 : List Nat := [1, 1, 2, 3, 1, 1, 2, 3, 1, 7]
def baseStart_438367 : Nat := 118140960795 + 438367 * 2 ^ 59
def prefixEnd_438367 : Nat := 4983230072969 + 3 ^ 40 * 438367 * 2
def baseEnd_438367 : Nat := 150061982713061080530995

theorem tailTrace_438367 : CollatzResearch.WordTrace tailWord_438367 prefixEnd_438367 150061982713061080530995 := by
  unfold tailWord_438367
  simp only [CollatzResearch.WordTrace]
  refine ⟨15988558002878700968233355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10659038668585800645488903 15988558002878700968233355)
  ·
    refine ⟨23982837004318051452350033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15988558002878700968233355 23982837004318051452350033)
    ·
      refine ⟨17987127753238538589262525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23982837004318051452350033 17987127753238538589262525)
      ·
        refine ⟨6745172907464451970973447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17987127753238538589262525 6745172907464451970973447)
        ·
          refine ⟨10117759361196677956460171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6745172907464451970973447 10117759361196677956460171)
          ·
            refine ⟨15176639041795016934690257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10117759361196677956460171 15176639041795016934690257)
            ·
              refine ⟨11382479281346262701017693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15176639041795016934690257 11382479281346262701017693)
              ·
                refine ⟨4268429730504848512881635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11382479281346262701017693 4268429730504848512881635)
                ·
                  refine ⟨6402644595757272769322453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4268429730504848512881635 6402644595757272769322453)
                  ·
                    refine ⟨150061982713061080530995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6402644595757272769322453 150061982713061080530995)
                    ·
                      rfl

theorem cell22_438367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 7].length) (baseStart_438367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_438367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_438367 prefixEnd_438367 := by exact prefixLift 438367
  have htrace : WordTrace (prefixWord ++ tailWord_438367) baseStart_438367 baseEnd_438367 := by
    simpa [prefixWord, tailWord_438367, baseEnd_438367] using wordTrace_append hprefix tailTrace_438367
  have hstable : (prefixWord ++ tailWord_438367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438367).length < 2 ^ (prefixWord ++ tailWord_438367).sum := by decide
  have hdescent : baseEnd_438367 < baseStart_438367 := by decide
  rcases family_descends (prefixWord ++ tailWord_438367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438390 : List Nat := [5, 1, 1, 2, 1, 2, 3, 3, 1, 3]
def baseStart_438390 : Nat := 118140960795 + 438390 * 2 ^ 59
def prefixEnd_438390 : Nat := 4983230072969 + 3 ^ 40 * 438390 * 2
def baseEnd_438390 : Nat := 150069856083096687205925

theorem tailTrace_438390 : CollatzResearch.WordTrace tailWord_438390 prefixEnd_438390 150069856083096687205925 := by
  unfold tailWord_438390
  simp only [CollatzResearch.WordTrace]
  refine ⟨999337305112210993520039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10659597921196917264213749 999337305112210993520039)
  ·
    refine ⟨1499005957668316490280059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 999337305112210993520039 1499005957668316490280059)
    ·
      refine ⟨2248508936502474735420089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1499005957668316490280059 2248508936502474735420089)
      ·
        refine ⟨1686381702376856051565067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2248508936502474735420089 1686381702376856051565067)
        ·
          refine ⟨2529572553565284077347601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1686381702376856051565067 2529572553565284077347601)
          ·
            refine ⟨1897179415173963058010701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2529572553565284077347601 1897179415173963058010701)
            ·
              refine ⟨711442280690236146754013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1897179415173963058010701 711442280690236146754013)
              ·
                refine ⟨266790855258838555032755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 711442280690236146754013 266790855258838555032755)
                ·
                  refine ⟨400186282888257832549133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 266790855258838555032755 400186282888257832549133)
                  ·
                    refine ⟨150069856083096687205925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 400186282888257832549133 150069856083096687205925)
                    ·
                      rfl

theorem cell22_438390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 3, 1, 3].length) (baseStart_438390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_438390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_438390 prefixEnd_438390 := by exact prefixLift 438390
  have htrace : WordTrace (prefixWord ++ tailWord_438390) baseStart_438390 baseEnd_438390 := by
    simpa [prefixWord, tailWord_438390, baseEnd_438390] using wordTrace_append hprefix tailTrace_438390
  have hstable : (prefixWord ++ tailWord_438390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438390).length < 2 ^ (prefixWord ++ tailWord_438390).sum := by decide
  have hdescent : baseEnd_438390 < baseStart_438390 := by decide
  rcases family_descends (prefixWord ++ tailWord_438390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438433 : List Nat := [1, 2, 3, 3, 1, 4, 1, 2, 1, 4]
def baseStart_438433 : Nat := 118140960795 + 438433 * 2 ^ 59
def prefixEnd_438433 : Nat := 4983230072969 + 3 ^ 40 * 438433 * 2
def baseEnd_438433 : Nat := 150084575861858908380793

theorem tailTrace_438433 : CollatzResearch.WordTrace tailWord_438433 prefixEnd_438433 150084575861858908380793 := by
  unfold tailWord_438433
  simp only [CollatzResearch.WordTrace]
  refine ⟨15990965220639594240135953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10660643480426396160090635 15990965220639594240135953)
  ·
    refine ⟨11993223915479695680101965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15990965220639594240135953 11993223915479695680101965)
    ·
      refine ⟨4497458968304885880038237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11993223915479695680101965 4497458968304885880038237)
      ·
        refine ⟨1686547113114332205014339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4497458968304885880038237 1686547113114332205014339)
        ·
          refine ⟨2529820669671498307521509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1686547113114332205014339 2529820669671498307521509)
          ·
            refine ⟨474341375563405932660283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2529820669671498307521509 474341375563405932660283)
            ·
              refine ⟨711512063345108898990425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 474341375563405932660283 711512063345108898990425)
              ·
                refine ⟨533634047508831674242819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 711512063345108898990425 533634047508831674242819)
                ·
                  refine ⟨800451071263247511364229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 533634047508831674242819 800451071263247511364229)
                  ·
                    refine ⟨150084575861858908380793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 800451071263247511364229 150084575861858908380793)
                    ·
                      rfl

theorem cell22_438433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 2, 1, 4].length) (baseStart_438433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_438433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_438433 prefixEnd_438433 := by exact prefixLift 438433
  have htrace : WordTrace (prefixWord ++ tailWord_438433) baseStart_438433 baseEnd_438433 := by
    simpa [prefixWord, tailWord_438433, baseEnd_438433] using wordTrace_append hprefix tailTrace_438433
  have hstable : (prefixWord ++ tailWord_438433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438433).length < 2 ^ (prefixWord ++ tailWord_438433).sum := by decide
  have hdescent : baseEnd_438433 < baseStart_438433 := by decide
  rcases family_descends (prefixWord ++ tailWord_438433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438465 : List Nat := [1, 2, 6, 1, 2, 1, 1, 4, 4]
def baseStart_438465 : Nat := 118140960795 + 438465 * 2 ^ 59
def prefixEnd_438465 : Nat := 4983230072969 + 3 ^ 40 * 438465 * 2
def baseEnd_438465 : Nat := 50031843371940497193565

theorem tailTrace_438465 : CollatzResearch.WordTrace tailWord_438465 prefixEnd_438465 50031843371940497193565 := by
  unfold tailWord_438465
  simp only [CollatzResearch.WordTrace]
  refine ⟨15992132356523663705300849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10661421571015775803533899 15992132356523663705300849)
  ·
    refine ⟨11994099267392747778975637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15992132356523663705300849 11994099267392747778975637)
    ·
      refine ⟨562223403159035052139483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11994099267392747778975637 562223403159035052139483)
      ·
        refine ⟨843335104738552578209225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 562223403159035052139483 843335104738552578209225)
        ·
          refine ⟨632501328553914433656919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 843335104738552578209225 632501328553914433656919)
          ·
            refine ⟨948751992830871650485379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 632501328553914433656919 948751992830871650485379)
            ·
              refine ⟨1423127989246307475728069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 948751992830871650485379 1423127989246307475728069)
              ·
                refine ⟨266836497983682651699013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1423127989246307475728069 266836497983682651699013)
                ·
                  refine ⟨50031843371940497193565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 266836497983682651699013 50031843371940497193565)
                  ·
                    rfl

theorem cell22_438465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 4, 4].length) (baseStart_438465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_438465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_438465 prefixEnd_438465 := by exact prefixLift 438465
  have htrace : WordTrace (prefixWord ++ tailWord_438465) baseStart_438465 baseEnd_438465 := by
    simpa [prefixWord, tailWord_438465, baseEnd_438465] using wordTrace_append hprefix tailTrace_438465
  have hstable : (prefixWord ++ tailWord_438465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438465).length < 2 ^ (prefixWord ++ tailWord_438465).sum := by decide
  have hdescent : baseEnd_438465 < baseStart_438465 := by decide
  rcases family_descends (prefixWord ++ tailWord_438465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438493 : List Nat := [1, 4, 3, 2, 1, 2, 3, 6]
def baseStart_438493 : Nat := 118140960795 + 438493 * 2 ^ 59
def prefixEnd_438493 : Nat := 4983230072969 + 3 ^ 40 * 438493 * 2
def baseEnd_438493 : Nat := 16678346120893194653401

theorem tailTrace_438493 : CollatzResearch.WordTrace tailWord_438493 prefixEnd_438493 16678346120893194653401 := by
  unfold tailWord_438493
  simp only [CollatzResearch.WordTrace]
  refine ⟨15993153600422224487320133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10662102400281482991546755 15993153600422224487320133)
  ·
    refine ⟨2998716300079167091372525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15993153600422224487320133 2998716300079167091372525)
    ·
      refine ⟨1124518612529687659264697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2998716300079167091372525 1124518612529687659264697)
      ·
        refine ⟨843388959397265744448523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1124518612529687659264697 843388959397265744448523)
        ·
          refine ⟨1265083439095898616672785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 843388959397265744448523 1265083439095898616672785)
          ·
            refine ⟨948812579321923962504589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1265083439095898616672785 948812579321923962504589)
            ·
              refine ⟨355804717245721485939221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 948812579321923962504589 355804717245721485939221)
              ·
                refine ⟨16678346120893194653401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 355804717245721485939221 16678346120893194653401)
                ·
                  rfl

theorem cell22_438493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3, 6].length) (baseStart_438493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_438493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_438493 prefixEnd_438493 := by exact prefixLift 438493
  have htrace : WordTrace (prefixWord ++ tailWord_438493) baseStart_438493 baseEnd_438493 := by
    simpa [prefixWord, tailWord_438493, baseEnd_438493] using wordTrace_append hprefix tailTrace_438493
  have hstable : (prefixWord ++ tailWord_438493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438493).length < 2 ^ (prefixWord ++ tailWord_438493).sum := by decide
  have hdescent : baseEnd_438493 < baseStart_438493 := by decide
  rcases family_descends (prefixWord ++ tailWord_438493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
