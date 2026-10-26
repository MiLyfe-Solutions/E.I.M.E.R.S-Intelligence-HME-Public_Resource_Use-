import V185TrunkScan22Chunk149

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1340069 : List Nat := [1, 3, 1, 2, 1, 2, 1, 3, 1, 7]
def baseStart_1340069 : Nat := 118140960795 + 1340069 * 2 ^ 59
def prefixEnd_1340069 : Nat := 4983230072969 + 3 ^ 40 * 1340069 * 2
def baseEnd_1340069 : Nat := 458733004793348471716427

theorem tailTrace_1340069 : CollatzResearch.WordTrace tailWord_1340069 prefixEnd_1340069 458733004793348471716427 := by
  unfold tailWord_1340069
  simp only [CollatzResearch.WordTrace]
  refine ⟨48876331782166353409391261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32584221188110902272927507 48876331782166353409391261)
  ·
    refine ⟨18328624418312382528521723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48876331782166353409391261 18328624418312382528521723)
    ·
      refine ⟨27492936627468573792782585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18328624418312382528521723 27492936627468573792782585)
      ·
        refine ⟨20619702470601430344586939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27492936627468573792782585 20619702470601430344586939)
        ·
          refine ⟨30929553705902145516880409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20619702470601430344586939 30929553705902145516880409)
          ·
            refine ⟨23197165279426609137660307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30929553705902145516880409 23197165279426609137660307)
            ·
              refine ⟨34795747919139913706490461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23197165279426609137660307 34795747919139913706490461)
              ·
                refine ⟨13048405469677467639933923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34795747919139913706490461 13048405469677467639933923)
                ·
                  refine ⟨19572608204516201459900885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13048405469677467639933923 19572608204516201459900885)
                  ·
                    refine ⟨458733004793348471716427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19572608204516201459900885 458733004793348471716427)
                    ·
                      rfl

theorem cell22_1340069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 7].length) (baseStart_1340069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1340069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1340069 prefixEnd_1340069 := by exact prefixLift 1340069
  have htrace : WordTrace (prefixWord ++ tailWord_1340069) baseStart_1340069 baseEnd_1340069 := by
    simpa [prefixWord, tailWord_1340069, baseEnd_1340069] using wordTrace_append hprefix tailTrace_1340069
  have hstable : (prefixWord ++ tailWord_1340069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340069).length < 2 ^ (prefixWord ++ tailWord_1340069).sum := by decide
  have hdescent : baseEnd_1340069 < baseStart_1340069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340109 : List Nat := [1, 6, 2, 1, 2, 1, 1, 4, 1, 3]
def baseStart_1340109 : Nat := 118140960795 + 1340109 * 2 ^ 59
def prefixEnd_1340109 : Nat := 4983230072969 + 3 ^ 40 * 1340109 * 2
def baseEnd_1340109 : Nat := 458746697610801700716305

theorem tailTrace_1340109 : CollatzResearch.WordTrace tailWord_1340109 prefixEnd_1340109 458746697610801700716305 := by
  unfold tailWord_1340109
  simp only [CollatzResearch.WordTrace]
  refine ⟨48877790702021440240847381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32585193801347626827231587 48877790702021440240847381)
  ·
    refine ⟨2291146439157255011289721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 48877790702021440240847381 2291146439157255011289721)
    ·
      refine ⟨1718359829367941258467291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2291146439157255011289721 1718359829367941258467291)
      ·
        refine ⟨2577539744051911887700937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1718359829367941258467291 2577539744051911887700937)
        ·
          refine ⟨1933154808038933915775703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2577539744051911887700937 1933154808038933915775703)
          ·
            refine ⟨2899732212058400873663555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1933154808038933915775703 2899732212058400873663555)
            ·
              refine ⟨4349598318087601310495333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2899732212058400873663555 4349598318087601310495333)
              ·
                refine ⟨815549684641425245717875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4349598318087601310495333 815549684641425245717875)
                ·
                  refine ⟨1223324526962137868576813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 815549684641425245717875 1223324526962137868576813)
                  ·
                    refine ⟨458746697610801700716305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1223324526962137868576813 458746697610801700716305)
                    ·
                      rfl

theorem cell22_1340109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_1340109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1340109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1340109 prefixEnd_1340109 := by exact prefixLift 1340109
  have htrace : WordTrace (prefixWord ++ tailWord_1340109) baseStart_1340109 baseEnd_1340109 := by
    simpa [prefixWord, tailWord_1340109, baseEnd_1340109] using wordTrace_append hprefix tailTrace_1340109
  have hstable : (prefixWord ++ tailWord_1340109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340109).length < 2 ^ (prefixWord ++ tailWord_1340109).sum := by decide
  have hdescent : baseEnd_1340109 < baseStart_1340109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340150 : List Nat := [5, 1, 1, 1, 1, 2, 4, 3, 4]
def baseStart_1340150 : Nat := 118140960795 + 1340150 * 2 ^ 59
def prefixEnd_1340150 : Nat := 4983230072969 + 3 ^ 40 * 1340150 * 2
def baseEnd_1340150 : Nat := 152920244249563753480393

theorem tailTrace_1340150 : CollatzResearch.WordTrace tailWord_1340150 prefixEnd_1340150 152920244249563753480393 := by
  unfold tailWord_1340150
  simp only [CollatzResearch.WordTrace]
  refine ⟨3054955380929556515193119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32586190729915269495393269 3054955380929556515193119)
  ·
    refine ⟨4582433071394334772789679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3054955380929556515193119 4582433071394334772789679)
    ·
      refine ⟨6873649607091502159184519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4582433071394334772789679 6873649607091502159184519)
      ·
        refine ⟨10310474410637253238776779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6873649607091502159184519 10310474410637253238776779)
        ·
          refine ⟨15465711615955879858165169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10310474410637253238776779 15465711615955879858165169)
          ·
            refine ⟨11599283711966909893623877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15465711615955879858165169 11599283711966909893623877)
            ·
              refine ⟨2174865695993795605054477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11599283711966909893623877 2174865695993795605054477)
              ·
                refine ⟨815574635997673351895429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2174865695993795605054477 815574635997673351895429)
                ·
                  refine ⟨152920244249563753480393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 815574635997673351895429 152920244249563753480393)
                  ·
                    rfl

theorem cell22_1340150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_1340150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1340150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1340150 prefixEnd_1340150 := by exact prefixLift 1340150
  have htrace : WordTrace (prefixWord ++ tailWord_1340150) baseStart_1340150 baseEnd_1340150 := by
    simpa [prefixWord, tailWord_1340150, baseEnd_1340150] using wordTrace_append hprefix tailTrace_1340150
  have hstable : (prefixWord ++ tailWord_1340150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340150).length < 2 ^ (prefixWord ++ tailWord_1340150).sum := by decide
  have hdescent : baseEnd_1340150 < baseStart_1340150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340193 : List Nat := [1, 2, 3, 2, 1, 2, 1, 4, 3, 3]
def baseStart_1340193 : Nat := 118140960795 + 1340193 * 2 ^ 59
def prefixEnd_1340193 : Nat := 4983230072969 + 3 ^ 40 * 1340193 * 2
def baseEnd_1340193 : Nat := 458775452527453481616047

theorem tailTrace_1340193 : CollatzResearch.WordTrace tailWord_1340193 prefixEnd_1340193 458775452527453481616047 := by
  unfold tailWord_1340193
  simp only [CollatzResearch.WordTrace]
  refine ⟨48880854433717122586905233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32587236289144748391270155 48880854433717122586905233)
  ·
    refine ⟨36660640825287841940178925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48880854433717122586905233 36660640825287841940178925)
    ·
      refine ⟨13747740309482940727567097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36660640825287841940178925 13747740309482940727567097)
      ·
        refine ⟨10310805232112205545675323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13747740309482940727567097 10310805232112205545675323)
        ·
          refine ⟨15466207848168308318512985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10310805232112205545675323 15466207848168308318512985)
          ·
            refine ⟨11599655886126231238884739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15466207848168308318512985 11599655886126231238884739)
            ·
              refine ⟨17399483829189346858327109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11599655886126231238884739 17399483829189346858327109)
              ·
                refine ⟨3262403217973002535936333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17399483829189346858327109 3262403217973002535936333)
                ·
                  refine ⟨1223401206739875950976125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3262403217973002535936333 1223401206739875950976125)
                  ·
                    refine ⟨458775452527453481616047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1223401206739875950976125 458775452527453481616047)
                    ·
                      rfl

theorem cell22_1340193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4, 3, 3].length) (baseStart_1340193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1340193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1340193 prefixEnd_1340193 := by exact prefixLift 1340193
  have htrace : WordTrace (prefixWord ++ tailWord_1340193) baseStart_1340193 baseEnd_1340193 := by
    simpa [prefixWord, tailWord_1340193, baseEnd_1340193] using wordTrace_append hprefix tailTrace_1340193
  have hstable : (prefixWord ++ tailWord_1340193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340193).length < 2 ^ (prefixWord ++ tailWord_1340193).sum := by decide
  have hdescent : baseEnd_1340193 < baseStart_1340193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340227 : List Nat := [1, 1, 1, 3, 1, 4, 5, 2, 1, 3]
def baseStart_1340227 : Nat := 118140960795 + 1340227 * 2 ^ 59
def prefixEnd_1340227 : Nat := 4983230072969 + 3 ^ 40 * 1340227 * 2
def baseEnd_1340227 : Nat := 458787091422288726265943

theorem tailTrace_1340227 : CollatzResearch.WordTrace tailWord_1340227 prefixEnd_1340227 458787091422288726265943 := by
  unfold tailWord_1340227
  simp only [CollatzResearch.WordTrace]
  refine ⟨48882094515593946393642935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32588063010395964262428623 48882094515593946393642935)
  ·
    refine ⟨73323141773390919590464403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48882094515593946393642935 73323141773390919590464403)
    ·
      refine ⟨109984712660086379385696605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73323141773390919590464403 109984712660086379385696605)
      ·
        refine ⟨41244267247532392269636227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109984712660086379385696605 41244267247532392269636227)
        ·
          refine ⟨61866400871298588404454341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41244267247532392269636227 61866400871298588404454341)
          ·
            refine ⟨11599950163368485325835189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61866400871298588404454341 11599950163368485325835189)
            ·
              refine ⟨1087495327815795499297049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11599950163368485325835189 1087495327815795499297049)
              ·
                refine ⟨815621495861846624472787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1087495327815795499297049 815621495861846624472787)
                ·
                  refine ⟨1223432243792769936709181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 815621495861846624472787 1223432243792769936709181)
                  ·
                    refine ⟨458787091422288726265943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1223432243792769936709181 458787091422288726265943)
                    ·
                      rfl

theorem cell22_1340227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 2, 1, 3].length) (baseStart_1340227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1340227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1340227 prefixEnd_1340227 := by exact prefixLift 1340227
  have htrace : WordTrace (prefixWord ++ tailWord_1340227) baseStart_1340227 baseEnd_1340227 := by
    simpa [prefixWord, tailWord_1340227, baseEnd_1340227] using wordTrace_append hprefix tailTrace_1340227
  have hstable : (prefixWord ++ tailWord_1340227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340227).length < 2 ^ (prefixWord ++ tailWord_1340227).sum := by decide
  have hdescent : baseEnd_1340227 < baseStart_1340227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340283 : List Nat := [1, 1, 1, 1, 1, 5, 2, 3, 4, 3]
def baseStart_1340283 : Nat := 118140960795 + 1340283 * 2 ^ 59
def prefixEnd_1340283 : Nat := 4983230072969 + 3 ^ 40 * 1340283 * 2
def baseEnd_1340283 : Nat := 458806261366723246865771

theorem tailTrace_1340283 : CollatzResearch.WordTrace tailWord_1340283 prefixEnd_1340283 458806261366723246865771 := by
  unfold tailWord_1340283
  simp only [CollatzResearch.WordTrace]
  refine ⟨48884137003391067957681503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32589424668927378638454335 48884137003391067957681503)
  ·
    refine ⟨73326205505086601936522255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48884137003391067957681503 73326205505086601936522255)
    ·
      refine ⟨109989308257629902904783383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73326205505086601936522255 109989308257629902904783383)
      ·
        refine ⟨164983962386444854357175075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109989308257629902904783383 164983962386444854357175075)
        ·
          refine ⟨247475943579667281535762613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164983962386444854357175075 247475943579667281535762613)
          ·
            refine ⟨23200869710593807643977745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 247475943579667281535762613 23200869710593807643977745)
            ·
              refine ⟨17400652282945355732983309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23200869710593807643977745 17400652282945355732983309)
              ·
                refine ⟨6525244606104508399868741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17400652282945355732983309 6525244606104508399868741)
                ·
                  refine ⟨1223483363644595324975389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6525244606104508399868741 1223483363644595324975389)
                  ·
                    refine ⟨458806261366723246865771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1223483363644595324975389 458806261366723246865771)
                    ·
                      rfl

theorem cell22_1340283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 4, 3].length) (baseStart_1340283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1340283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1340283 prefixEnd_1340283 := by exact prefixLift 1340283
  have htrace : WordTrace (prefixWord ++ tailWord_1340283) baseStart_1340283 baseEnd_1340283 := by
    simpa [prefixWord, tailWord_1340283, baseEnd_1340283] using wordTrace_append hprefix tailTrace_1340283
  have hstable : (prefixWord ++ tailWord_1340283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340283).length < 2 ^ (prefixWord ++ tailWord_1340283).sum := by decide
  have hdescent : baseEnd_1340283 < baseStart_1340283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340300 : List Nat := [2, 2, 1, 2, 1, 2, 4, 3, 2, 3]
def baseStart_1340300 : Nat := 118140960795 + 1340300 * 2 ^ 59
def prefixEnd_1340300 : Nat := 4983230072969 + 3 ^ 40 * 1340300 * 2
def baseEnd_1340300 : Nat := 458812080814140869190719

theorem tailTrace_1340300 : CollatzResearch.WordTrace tailWord_1340300 prefixEnd_1340300 458812080814140869190719 := by
  unfold tailWord_1340300
  simp only [CollatzResearch.WordTrace]
  refine ⟨24442378522164739930525177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32589838029552986574033569 24442378522164739930525177)
  ·
    refine ⟨18331783891623554947893883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24442378522164739930525177 18331783891623554947893883)
    ·
      refine ⟨27497675837435332421840825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18331783891623554947893883 27497675837435332421840825)
      ·
        refine ⟨20623256878076499316380619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27497675837435332421840825 20623256878076499316380619)
        ·
          refine ⟨30934885317114748974570929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20623256878076499316380619 30934885317114748974570929)
          ·
            refine ⟨23201163987836061730928197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30934885317114748974570929 23201163987836061730928197)
            ·
              refine ⟨4350218247719261574549037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23201163987836061730928197 4350218247719261574549037)
              ·
                refine ⟨1631331842894723090455889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4350218247719261574549037 1631331842894723090455889)
                ·
                  refine ⟨1223498882171042317841917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1631331842894723090455889 1223498882171042317841917)
                  ·
                    refine ⟨458812080814140869190719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1223498882171042317841917 458812080814140869190719)
                    ·
                      rfl

theorem cell22_1340300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 3, 2, 3].length) (baseStart_1340300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1340300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1340300 prefixEnd_1340300 := by exact prefixLift 1340300
  have htrace : WordTrace (prefixWord ++ tailWord_1340300) baseStart_1340300 baseEnd_1340300 := by
    simpa [prefixWord, tailWord_1340300, baseEnd_1340300] using wordTrace_append hprefix tailTrace_1340300
  have hstable : (prefixWord ++ tailWord_1340300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340300).length < 2 ^ (prefixWord ++ tailWord_1340300).sum := by decide
  have hdescent : baseEnd_1340300 < baseStart_1340300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340345 : List Nat := [1, 2, 1, 4, 2, 2, 1, 3, 3, 3]
def baseStart_1340345 : Nat := 118140960795 + 1340345 * 2 ^ 59
def prefixEnd_1340345 : Nat := 4983230072969 + 3 ^ 40 * 1340345 * 2
def baseEnd_1340345 : Nat := 458827485233775751815581

theorem tailTrace_1340345 : CollatzResearch.WordTrace tailWord_1340345 prefixEnd_1340345 458827485233775751815581 := by
  unfold tailWord_1340345
  simp only [CollatzResearch.WordTrace]
  refine ⟨48886398329166452546438489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32590932219444301697625659 48886398329166452546438489)
  ·
    refine ⟨36664798746874839409828867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48886398329166452546438489 36664798746874839409828867)
    ·
      refine ⟨54997198120312259114743301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36664798746874839409828867 54997198120312259114743301)
      ·
        refine ⟨10311974647558548584014369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54997198120312259114743301 10311974647558548584014369)
        ·
          refine ⟨7733980985668911438010777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10311974647558548584014369 7733980985668911438010777)
          ·
            refine ⟨5800485739251683578508083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7733980985668911438010777 5800485739251683578508083)
            ·
              refine ⟨8700728608877525367762125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5800485739251683578508083 8700728608877525367762125)
              ·
                refine ⟨3262773228329072012910797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8700728608877525367762125 3262773228329072012910797)
                ·
                  refine ⟨1223539960623402004841549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3262773228329072012910797 1223539960623402004841549)
                  ·
                    refine ⟨458827485233775751815581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1223539960623402004841549 458827485233775751815581)
                    ·
                      rfl

theorem cell22_1340345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 3, 3, 3].length) (baseStart_1340345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1340345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1340345 prefixEnd_1340345 := by exact prefixLift 1340345
  have htrace : WordTrace (prefixWord ++ tailWord_1340345) baseStart_1340345 baseEnd_1340345 := by
    simpa [prefixWord, tailWord_1340345, baseEnd_1340345] using wordTrace_append hprefix tailTrace_1340345
  have hstable : (prefixWord ++ tailWord_1340345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340345).length < 2 ^ (prefixWord ++ tailWord_1340345).sum := by decide
  have hdescent : baseEnd_1340345 < baseStart_1340345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340433 : List Nat := [1, 2, 2, 1, 1, 2, 1, 5, 1, 6]
def baseStart_1340433 : Nat := 118140960795 + 1340433 * 2 ^ 59
def prefixEnd_1340433 : Nat := 4983230072969 + 3 ^ 40 * 1340433 * 2
def baseEnd_1340433 : Nat := 458857609432172855615311

theorem tailTrace_1340433 : CollatzResearch.WordTrace tailWord_1340433 prefixEnd_1340433 458857609432172855615311 := by
  unfold tailWord_1340433
  simp only [CollatzResearch.WordTrace]
  refine ⟨48889607952847643575641953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32593071968565095717094635 48889607952847643575641953)
  ·
    refine ⟨36667205964635732681731465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48889607952847643575641953 36667205964635732681731465)
    ·
      refine ⟨27500404473476799511298599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36667205964635732681731465 27500404473476799511298599)
      ·
        refine ⟨41250606710215199266947899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27500404473476799511298599 41250606710215199266947899)
        ·
          refine ⟨61875910065322798900421849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41250606710215199266947899 61875910065322798900421849)
          ·
            refine ⟨46406932548992099175316387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61875910065322798900421849 46406932548992099175316387)
            ·
              refine ⟨69610398823488148762974581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46406932548992099175316387 69610398823488148762974581)
              ·
                refine ⟨6525974889702013946528867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69610398823488148762974581 6525974889702013946528867)
                ·
                  refine ⟨9788962334553020919793301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6525974889702013946528867 9788962334553020919793301)
                  ·
                    refine ⟨458857609432172855615311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9788962334553020919793301 458857609432172855615311)
                    ·
                      rfl

theorem cell22_1340433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 6].length) (baseStart_1340433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1340433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1340433 prefixEnd_1340433 := by exact prefixLift 1340433
  have htrace : WordTrace (prefixWord ++ tailWord_1340433) baseStart_1340433 baseEnd_1340433 := by
    simpa [prefixWord, tailWord_1340433, baseEnd_1340433] using wordTrace_append hprefix tailTrace_1340433
  have hstable : (prefixWord ++ tailWord_1340433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340433).length < 2 ^ (prefixWord ++ tailWord_1340433).sum := by decide
  have hdescent : baseEnd_1340433 < baseStart_1340433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340439 : List Nat := [1, 1, 3, 5, 1, 2, 3, 1, 1, 4]
def baseStart_1340439 : Nat := 118140960795 + 1340439 * 2 ^ 59
def prefixEnd_1340439 : Nat := 4983230072969 + 3 ^ 40 * 1340439 * 2
def baseEnd_1340439 : Nat := 458859663354790839965293

theorem tailTrace_1340439 : CollatzResearch.WordTrace tailWord_1340439 prefixEnd_1340439 458859663354790839965293 := by
  unfold tailWord_1340439
  simp only [CollatzResearch.WordTrace]
  refine ⟨48889826790825906600360371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32593217860550604400240247 48889826790825906600360371)
  ·
    refine ⟨73334740186238859900540557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48889826790825906600360371 73334740186238859900540557)
    ·
      refine ⟨27500527569839572462702709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73334740186238859900540557 27500527569839572462702709)
      ·
        refine ⟨2578174459672459918378379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27500527569839572462702709 2578174459672459918378379)
        ·
          refine ⟨3867261689508689877567569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2578174459672459918378379 3867261689508689877567569)
          ·
            refine ⟨2900446267131517408175677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3867261689508689877567569 2900446267131517408175677)
            ·
              refine ⟨1087667350174319028065879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2900446267131517408175677 1087667350174319028065879)
              ·
                refine ⟨1631501025261478542098819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1087667350174319028065879 1631501025261478542098819)
                ·
                  refine ⟨2447251537892217813148229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1631501025261478542098819 2447251537892217813148229)
                  ·
                    refine ⟨458859663354790839965293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2447251537892217813148229 458859663354790839965293)
                    ·
                      rfl

theorem cell22_1340439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3, 1, 1, 4].length) (baseStart_1340439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1340439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1340439 prefixEnd_1340439 := by exact prefixLift 1340439
  have htrace : WordTrace (prefixWord ++ tailWord_1340439) baseStart_1340439 baseEnd_1340439 := by
    simpa [prefixWord, tailWord_1340439, baseEnd_1340439] using wordTrace_append hprefix tailTrace_1340439
  have hstable : (prefixWord ++ tailWord_1340439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340439).length < 2 ^ (prefixWord ++ tailWord_1340439).sum := by decide
  have hdescent : baseEnd_1340439 < baseStart_1340439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340514 : List Nat := [3, 3, 2, 2, 1, 1, 1, 3, 3, 3]
def baseStart_1340514 : Nat := 118140960795 + 1340514 * 2 ^ 59
def prefixEnd_1340514 : Nat := 4983230072969 + 3 ^ 40 * 1340514 * 2
def baseEnd_1340514 : Nat := 458885337387515644340063

theorem tailTrace_1340514 : CollatzResearch.WordTrace tailWord_1340514 prefixEnd_1340514 458885337387515644340063 := by
  unfold tailWord_1340514
  simp only [CollatzResearch.WordTrace]
  refine ⟨12223140566388548602335149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32595041510369462939560397 12223140566388548602335149)
  ·
    refine ⟨4583677712395705725875681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12223140566388548602335149 4583677712395705725875681)
    ·
      refine ⟨3437758284296779294406761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4583677712395705725875681 3437758284296779294406761)
      ·
        refine ⟨2578318713222584470805071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3437758284296779294406761 2578318713222584470805071)
        ·
          refine ⟨3867478069833876706207607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2578318713222584470805071 3867478069833876706207607)
          ·
            refine ⟨5801217104750815059311411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3867478069833876706207607 5801217104750815059311411)
            ·
              refine ⟨8701825657126222588967117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5801217104750815059311411 8701825657126222588967117)
              ·
                refine ⟨3263184621422333470862669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8701825657126222588967117 3263184621422333470862669)
                ·
                  refine ⟨1223694233033375051573501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3263184621422333470862669 1223694233033375051573501)
                  ·
                    refine ⟨458885337387515644340063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1223694233033375051573501 458885337387515644340063)
                    ·
                      rfl

theorem cell22_1340514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_1340514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1340514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1340514 prefixEnd_1340514 := by exact prefixLift 1340514
  have htrace : WordTrace (prefixWord ++ tailWord_1340514) baseStart_1340514 baseEnd_1340514 := by
    simpa [prefixWord, tailWord_1340514, baseEnd_1340514] using wordTrace_append hprefix tailTrace_1340514
  have hstable : (prefixWord ++ tailWord_1340514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340514).length < 2 ^ (prefixWord ++ tailWord_1340514).sum := by decide
  have hdescent : baseEnd_1340514 < baseStart_1340514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340527 : List Nat := [1, 1, 2, 1, 3, 3, 5, 1, 5]
def baseStart_1340527 : Nat := 118140960795 + 1340527 * 2 ^ 59
def prefixEnd_1340527 : Nat := 4983230072969 + 3 ^ 40 * 1340527 * 2
def baseEnd_1340527 : Nat := 152963262517729314588341

theorem tailTrace_1340527 : CollatzResearch.WordTrace tailWord_1340527 prefixEnd_1340527 152963262517729314588341 := by
  unfold tailWord_1340527
  simp only [CollatzResearch.WordTrace]
  refine ⟨48893036414507097629563835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32595357609671398419709223 48893036414507097629563835)
  ·
    refine ⟨73339554621760646444345753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48893036414507097629563835 73339554621760646444345753)
    ·
      refine ⟨55004665966320484833259315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73339554621760646444345753 55004665966320484833259315)
      ·
        refine ⟨82506998949480727249888973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55004665966320484833259315 82506998949480727249888973)
        ·
          refine ⟨30940124606055272718708365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82506998949480727249888973 30940124606055272718708365)
          ·
            refine ⟨11602546727270727269515637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30940124606055272718708365 11602546727270727269515637)
            ·
              refine ⟨1087738755681630681517091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11602546727270727269515637 1087738755681630681517091)
              ·
                refine ⟨1631608133522446022275637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1087738755681630681517091 1631608133522446022275637)
                ·
                  refine ⟨152963262517729314588341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1631608133522446022275637 152963262517729314588341)
                  ·
                    rfl

theorem cell22_1340527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5, 1, 5].length) (baseStart_1340527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1340527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1340527 prefixEnd_1340527 := by exact prefixLift 1340527
  have htrace : WordTrace (prefixWord ++ tailWord_1340527) baseStart_1340527 baseEnd_1340527 := by
    simpa [prefixWord, tailWord_1340527, baseEnd_1340527] using wordTrace_append hprefix tailTrace_1340527
  have hstable : (prefixWord ++ tailWord_1340527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340527).length < 2 ^ (prefixWord ++ tailWord_1340527).sum := by decide
  have hdescent : baseEnd_1340527 < baseStart_1340527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340572 : List Nat := [2, 2, 3, 2, 1, 2, 3, 1, 6]
def baseStart_1340572 : Nat := 118140960795 + 1340572 * 2 ^ 59
def prefixEnd_1340572 : Nat := 4983230072969 + 3 ^ 40 * 1340572 * 2
def baseEnd_1340572 : Nat := 152968397324274275463295

theorem tailTrace_1340572 : CollatzResearch.WordTrace tailWord_1340572 prefixEnd_1340572 152968397324274275463295 := by
  unfold tailWord_1340572
  simp only [CollatzResearch.WordTrace]
  refine ⟨24447338849672035157475985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32596451799562713543301313 24447338849672035157475985)
  ·
    refine ⟨18335504137254026368106989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24447338849672035157475985 18335504137254026368106989)
    ·
      refine ⟨6875814051470259888040121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18335504137254026368106989 6875814051470259888040121)
      ·
        refine ⟨5156860538602694916030091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6875814051470259888040121 5156860538602694916030091)
        ·
          refine ⟨7735290807904042374045137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5156860538602694916030091 7735290807904042374045137)
          ·
            refine ⟨5801468105928031780533853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7735290807904042374045137 5801468105928031780533853)
            ·
              refine ⟨2175550539723011917700195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5801468105928031780533853 2175550539723011917700195)
              ·
                refine ⟨3263325809584517876550293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2175550539723011917700195 3263325809584517876550293)
                ·
                  refine ⟨152968397324274275463295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3263325809584517876550293 152968397324274275463295)
                  ·
                    rfl

theorem cell22_1340572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 1, 6].length) (baseStart_1340572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1340572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1340572 prefixEnd_1340572 := by exact prefixLift 1340572
  have htrace : WordTrace (prefixWord ++ tailWord_1340572) baseStart_1340572 baseEnd_1340572 := by
    simpa [prefixWord, tailWord_1340572, baseEnd_1340572] using wordTrace_append hprefix tailTrace_1340572
  have hstable : (prefixWord ++ tailWord_1340572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340572).length < 2 ^ (prefixWord ++ tailWord_1340572).sum := by decide
  have hdescent : baseEnd_1340572 < baseStart_1340572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340578 : List Nat := [3, 3, 1, 3, 3, 1, 2, 1, 5]
def baseStart_1340578 : Nat := 118140960795 + 1340578 * 2 ^ 59
def prefixEnd_1340578 : Nat := 4983230072969 + 3 ^ 40 * 1340578 * 2
def baseEnd_1340578 : Nat := 152969081965146936913289

theorem tailTrace_1340578 : CollatzResearch.WordTrace tailWord_1340578 prefixEnd_1340578 152969081965146936913289 := by
  unfold tailWord_1340578
  simp only [CollatzResearch.WordTrace]
  refine ⟨12223724134330583334917597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32596597691548222226446925 12223724134330583334917597)
  ·
    refine ⟨4583896550373968750594099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12223724134330583334917597 4583896550373968750594099)
    ·
      refine ⟨6875844825560953125891149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4583896550373968750594099 6875844825560953125891149)
      ·
        refine ⟨2578441809585357422209181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6875844825560953125891149 2578441809585357422209181)
        ·
          refine ⟨966915678594509033328443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2578441809585357422209181 966915678594509033328443)
          ·
            refine ⟨1450373517891763549992665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 966915678594509033328443 1450373517891763549992665)
            ·
              refine ⟨1087780138418822662494499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1450373517891763549992665 1087780138418822662494499)
              ·
                refine ⟨1631670207628233993741749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1087780138418822662494499 1631670207628233993741749)
                ·
                  refine ⟨152969081965146936913289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1631670207628233993741749 152969081965146936913289)
                  ·
                    rfl

theorem cell22_1340578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_1340578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1340578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1340578 prefixEnd_1340578 := by exact prefixLift 1340578
  have htrace : WordTrace (prefixWord ++ tailWord_1340578) baseStart_1340578 baseEnd_1340578 := by
    simpa [prefixWord, tailWord_1340578, baseEnd_1340578] using wordTrace_append hprefix tailTrace_1340578
  have hstable : (prefixWord ++ tailWord_1340578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340578).length < 2 ^ (prefixWord ++ tailWord_1340578).sum := by decide
  have hdescent : baseEnd_1340578 < baseStart_1340578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340662 : List Nat := [5, 1, 1, 1, 1, 1, 1, 4, 7]
def baseStart_1340662 : Nat := 118140960795 + 1340662 * 2 ^ 59
def prefixEnd_1340662 : Nat := 4983230072969 + 3 ^ 40 * 1340662 * 2
def baseEnd_1340662 : Nat := 152978666937364197213203

theorem tailTrace_1340662 : CollatzResearch.WordTrace tailWord_1340662 prefixEnd_1340662 152978666937364197213203 := by
  unfold tailWord_1340662
  simp only [CollatzResearch.WordTrace]
  refine ⟨3056122516813625980358015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32598640179345343790485493 3056122516813625980358015)
  ·
    refine ⟨4584183775220438970537023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3056122516813625980358015 4584183775220438970537023)
    ·
      refine ⟨6876275662830658455805535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4584183775220438970537023 6876275662830658455805535)
      ·
        refine ⟨10314413494245987683708303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6876275662830658455805535 10314413494245987683708303)
        ·
          refine ⟨15471620241368981525562455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10314413494245987683708303 15471620241368981525562455)
          ·
            refine ⟨23207430362053472288343683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15471620241368981525562455 23207430362053472288343683)
            ·
              refine ⟨34811145543080208432515525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23207430362053472288343683 34811145543080208432515525)
              ·
                refine ⟨6527089789327539081096661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34811145543080208432515525 6527089789327539081096661)
                ·
                  refine ⟨152978666937364197213203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6527089789327539081096661 152978666937364197213203)
                  ·
                    rfl

theorem cell22_1340662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_1340662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1340662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1340662 prefixEnd_1340662 := by exact prefixLift 1340662
  have htrace : WordTrace (prefixWord ++ tailWord_1340662) baseStart_1340662 baseEnd_1340662 := by
    simpa [prefixWord, tailWord_1340662, baseEnd_1340662] using wordTrace_append hprefix tailTrace_1340662
  have hstable : (prefixWord ++ tailWord_1340662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340662).length < 2 ^ (prefixWord ++ tailWord_1340662).sum := by decide
  have hdescent : baseEnd_1340662 < baseStart_1340662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340666 : List Nat := [3, 1, 1, 1, 1, 4, 4, 3, 1, 3]
def baseStart_1340666 : Nat := 118140960795 + 1340666 * 2 ^ 59
def prefixEnd_1340666 : Nat := 4983230072969 + 3 ^ 40 * 1340666 * 2
def baseEnd_1340666 : Nat := 458937370093837914539597

theorem tailTrace_1340666 : CollatzResearch.WordTrace tailWord_1340666 prefixEnd_1340666 458937370093837914539597 := by
  unfold tailWord_1340666
  simp only [CollatzResearch.WordTrace]
  refine ⟨12224526540250881092218463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32598737440669016245915901 12224526540250881092218463)
  ·
    refine ⟨18336789810376321638327695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12224526540250881092218463 18336789810376321638327695)
    ·
      refine ⟨27505184715564482457491543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18336789810376321638327695 27505184715564482457491543)
      ·
        refine ⟨41257777073346723686237315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27505184715564482457491543 41257777073346723686237315)
        ·
          refine ⟨61886665610020085529355973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41257777073346723686237315 61886665610020085529355973)
          ·
            refine ⟨11603749801878766036754245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61886665610020085529355973 11603749801878766036754245)
            ·
              refine ⟨2175703087852268631891421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11603749801878766036754245 2175703087852268631891421)
              ·
                refine ⟨815888657944600736959283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2175703087852268631891421 815888657944600736959283)
                ·
                  refine ⟨1223832986916901105438925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 815888657944600736959283 1223832986916901105438925)
                  ·
                    refine ⟨458937370093837914539597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1223832986916901105438925 458937370093837914539597)
                    ·
                      rfl

theorem cell22_1340666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 3, 1, 3].length) (baseStart_1340666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1340666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1340666 prefixEnd_1340666 := by exact prefixLift 1340666
  have htrace : WordTrace (prefixWord ++ tailWord_1340666) baseStart_1340666 baseEnd_1340666 := by
    simpa [prefixWord, tailWord_1340666, baseEnd_1340666] using wordTrace_append hprefix tailTrace_1340666
  have hstable : (prefixWord ++ tailWord_1340666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340666).length < 2 ^ (prefixWord ++ tailWord_1340666).sum := by decide
  have hdescent : baseEnd_1340666 < baseStart_1340666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340707 : List Nat := [1, 1, 1, 4, 2, 3, 2, 2, 6]
def baseStart_1340707 : Nat := 118140960795 + 1340707 * 2 ^ 59
def prefixEnd_1340707 : Nat := 4983230072969 + 3 ^ 40 * 1340707 * 2
def baseEnd_1340707 : Nat := 152983801743909158088157

theorem tailTrace_1340707 : CollatzResearch.WordTrace tailWord_1340707 prefixEnd_1340707 152983801743909158088157 := by
  unfold tailWord_1340707
  simp only [CollatzResearch.WordTrace]
  refine ⟨48899601553854988371116375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32599734369236658914077583 48899601553854988371116375)
  ·
    refine ⟨73349402330782482556674563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48899601553854988371116375 73349402330782482556674563)
    ·
      refine ⟨110024103496173723835011845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73349402330782482556674563 110024103496173723835011845)
      ·
        refine ⟨20629519405532573219064721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110024103496173723835011845 20629519405532573219064721)
        ·
          refine ⟨15472139554149429914298541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20629519405532573219064721 15472139554149429914298541)
          ·
            refine ⟨5802052332806036217861953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15472139554149429914298541 5802052332806036217861953)
            ·
              refine ⟨4351539249604527163396465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5802052332806036217861953 4351539249604527163396465)
              ·
                refine ⟨3263654437203395372547349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4351539249604527163396465 3263654437203395372547349)
                ·
                  refine ⟨152983801743909158088157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3263654437203395372547349 152983801743909158088157)
                  ·
                    rfl

theorem cell22_1340707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 2, 6].length) (baseStart_1340707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1340707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1340707 prefixEnd_1340707 := by exact prefixLift 1340707
  have htrace : WordTrace (prefixWord ++ tailWord_1340707) baseStart_1340707 baseEnd_1340707 := by
    simpa [prefixWord, tailWord_1340707, baseEnd_1340707] using wordTrace_append hprefix tailTrace_1340707
  have hstable : (prefixWord ++ tailWord_1340707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340707).length < 2 ^ (prefixWord ++ tailWord_1340707).sum := by decide
  have hdescent : baseEnd_1340707 < baseStart_1340707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340709 : List Nat := [1, 3, 1, 2, 4, 1, 1, 4, 1, 4]
def baseStart_1340709 : Nat := 118140960795 + 1340709 * 2 ^ 59
def prefixEnd_1340709 : Nat := 4983230072969 + 3 ^ 40 * 1340709 * 2
def baseEnd_1340709 : Nat := 458952089872600135714465

theorem tailTrace_1340709 : CollatzResearch.WordTrace tailWord_1340709 prefixEnd_1340709 458952089872600135714465 := by
  unfold tailWord_1340709
  simp only [CollatzResearch.WordTrace]
  refine ⟨48899674499847742712689181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32599782999898495141792787 48899674499847742712689181)
  ·
    refine ⟨18337377937442903517258443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48899674499847742712689181 18337377937442903517258443)
    ·
      refine ⟨27506066906164355275887665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18337377937442903517258443 27506066906164355275887665)
      ·
        refine ⟨20629550179623266456915749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27506066906164355275887665 20629550179623266456915749)
        ·
          refine ⟨3868040658679362460671703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20629550179623266456915749 3868040658679362460671703)
          ·
            refine ⟨5802060988019043691007555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3868040658679362460671703 5802060988019043691007555)
            ·
              refine ⟨8703091482028565536511333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5802060988019043691007555 8703091482028565536511333)
              ·
                refine ⟨1631829652880356038095875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8703091482028565536511333 1631829652880356038095875)
                ·
                  refine ⟨2447744479320534057143813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1631829652880356038095875 2447744479320534057143813)
                  ·
                    refine ⟨458952089872600135714465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2447744479320534057143813 458952089872600135714465)
                    ·
                      rfl

theorem cell22_1340709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 4, 1, 4].length) (baseStart_1340709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1340709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1340709 prefixEnd_1340709 := by exact prefixLift 1340709
  have htrace : WordTrace (prefixWord ++ tailWord_1340709) baseStart_1340709 baseEnd_1340709 := by
    simpa [prefixWord, tailWord_1340709, baseEnd_1340709] using wordTrace_append hprefix tailTrace_1340709
  have hstable : (prefixWord ++ tailWord_1340709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340709).length < 2 ^ (prefixWord ++ tailWord_1340709).sum := by decide
  have hdescent : baseEnd_1340709 < baseStart_1340709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340739 : List Nat := [1, 1, 1, 3, 1, 3, 1, 6, 2, 3]
def baseStart_1340739 : Nat := 118140960795 + 1340739 * 2 ^ 59
def prefixEnd_1340739 : Nat := 4983230072969 + 3 ^ 40 * 1340739 * 2
def baseEnd_1340739 : Nat := 458962359485690057464373

theorem tailTrace_1340739 : CollatzResearch.WordTrace tailWord_1340739 prefixEnd_1340739 458962359485690057464373 := by
  unfold tailWord_1340739
  simp only [CollatzResearch.WordTrace]
  refine ⟨48900768689739057836281271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32600512459826038557520847 48900768689739057836281271)
  ·
    refine ⟨73351153034608586754421907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48900768689739057836281271 73351153034608586754421907)
    ·
      refine ⟨110026729551912880131632861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73351153034608586754421907 110026729551912880131632861)
      ·
        refine ⟨41260023581967330049362323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110026729551912880131632861 41260023581967330049362323)
        ·
          refine ⟨61890035372950995074043485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41260023581967330049362323 61890035372950995074043485)
          ·
            refine ⟨23208763264856623152766307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61890035372950995074043485 23208763264856623152766307)
            ·
              refine ⟨34813144897284934729149461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23208763264856623152766307 34813144897284934729149461)
              ·
                refine ⟨1631866167060231315428881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34813144897284934729149461 1631866167060231315428881)
                ·
                  refine ⟨1223899625295173486571661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1631866167060231315428881 1223899625295173486571661)
                  ·
                    refine ⟨458962359485690057464373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1223899625295173486571661 458962359485690057464373)
                    ·
                      rfl

theorem cell22_1340739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 6, 2, 3].length) (baseStart_1340739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1340739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1340739 prefixEnd_1340739 := by exact prefixLift 1340739
  have htrace : WordTrace (prefixWord ++ tailWord_1340739) baseStart_1340739 baseEnd_1340739 := by
    simpa [prefixWord, tailWord_1340739, baseEnd_1340739] using wordTrace_append hprefix tailTrace_1340739
  have hstable : (prefixWord ++ tailWord_1340739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340739).length < 2 ^ (prefixWord ++ tailWord_1340739).sum := by decide
  have hdescent : baseEnd_1340739 < baseStart_1340739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340752 : List Nat := [2, 1, 1, 1, 1, 5, 4, 7]
def baseStart_1340752 : Nat := 118140960795 + 1340752 * 2 ^ 59
def prefixEnd_1340752 : Nat := 4983230072969 + 3 ^ 40 * 1340752 * 2
def baseEnd_1340752 : Nat := 50996312183484706321037

theorem tailTrace_1340752 : CollatzResearch.WordTrace tailWord_1340752 prefixEnd_1340752 50996312183484706321037 := by
  unfold tailWord_1340752
  simp only [CollatzResearch.WordTrace]
  refine ⟨24450621419345980528252255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32600828559127974037669673 24450621419345980528252255)
  ·
    refine ⟨36675932129018970792378383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24450621419345980528252255 36675932129018970792378383)
    ·
      refine ⟨55013898193528456188567575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36675932129018970792378383 55013898193528456188567575)
      ·
        refine ⟨82520847290292684282851363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55013898193528456188567575 82520847290292684282851363)
        ·
          refine ⟨123781270935439026424277045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82520847290292684282851363 123781270935439026424277045)
          ·
            refine ⟨11604494150197408727275973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 123781270935439026424277045 11604494150197408727275973)
            ·
              refine ⟨2175842653162014136364245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11604494150197408727275973 2175842653162014136364245)
              ·
                refine ⟨50996312183484706321037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2175842653162014136364245 50996312183484706321037)
                ·
                  rfl

theorem cell22_1340752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 7].length) (baseStart_1340752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1340752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1340752 prefixEnd_1340752 := by exact prefixLift 1340752
  have htrace : WordTrace (prefixWord ++ tailWord_1340752) baseStart_1340752 baseEnd_1340752 := by
    simpa [prefixWord, tailWord_1340752, baseEnd_1340752] using wordTrace_append hprefix tailTrace_1340752
  have hstable : (prefixWord ++ tailWord_1340752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340752).length < 2 ^ (prefixWord ++ tailWord_1340752).sum := by decide
  have hdescent : baseEnd_1340752 < baseStart_1340752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340756 : List Nat := [2, 4, 1, 1, 2, 1, 3, 3, 2, 3]
def baseStart_1340756 : Nat := 118140960795 + 1340756 * 2 ^ 59
def prefixEnd_1340756 : Nat := 4983230072969 + 3 ^ 40 * 1340756 * 2
def baseEnd_1340756 : Nat := 458968178933107679789321

theorem tailTrace_1340756 : CollatzResearch.WordTrace tailWord_1340756 prefixEnd_1340756 458968178933107679789321 := by
  unfold tailWord_1340756
  simp only [CollatzResearch.WordTrace]
  refine ⟨24450694365338734869825061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32600925820451646493100081 24450694365338734869825061)
  ·
    refine ⟨4584505193501012788092199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24450694365338734869825061 4584505193501012788092199)
    ·
      refine ⟨6876757790251519182138299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4584505193501012788092199 6876757790251519182138299)
      ·
        refine ⟨10315136685377278773207449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6876757790251519182138299 10315136685377278773207449)
        ·
          refine ⟨7736352514032959079905587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10315136685377278773207449 7736352514032959079905587)
          ·
            refine ⟨11604528771049438619858381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7736352514032959079905587 11604528771049438619858381)
            ·
              refine ⟨4351698289143539482446893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11604528771049438619858381 4351698289143539482446893)
              ·
                refine ⟨1631886858428827305917585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4351698289143539482446893 1631886858428827305917585)
                ·
                  refine ⟨1223915143821620479438189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1631886858428827305917585 1223915143821620479438189)
                  ·
                    refine ⟨458968178933107679789321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1223915143821620479438189 458968178933107679789321)
                    ·
                      rfl

theorem cell22_1340756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_1340756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1340756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1340756 prefixEnd_1340756 := by exact prefixLift 1340756
  have htrace : WordTrace (prefixWord ++ tailWord_1340756) baseStart_1340756 baseEnd_1340756 := by
    simpa [prefixWord, tailWord_1340756, baseEnd_1340756] using wordTrace_append hprefix tailTrace_1340756
  have hstable : (prefixWord ++ tailWord_1340756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340756).length < 2 ^ (prefixWord ++ tailWord_1340756).sum := by decide
  have hdescent : baseEnd_1340756 < baseStart_1340756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340889 : List Nat := [1, 2, 1, 2, 4, 2, 2, 1, 1, 6]
def baseStart_1340889 : Nat := 118140960795 + 1340889 * 2 ^ 59
def prefixEnd_1340889 : Nat := 4983230072969 + 3 ^ 40 * 1340889 * 2
def baseEnd_1340889 : Nat := 459013707551139666213913

theorem tailTrace_1340889 : CollatzResearch.WordTrace tailWord_1340889 prefixEnd_1340889 459013707551139666213913 := by
  unfold tailWord_1340889
  simp only [CollatzResearch.WordTrace]
  refine ⟨48906239639195633454241721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32604159759463755636161147 48906239639195633454241721)
  ·
    refine ⟨36679679729396725090681291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48906239639195633454241721 36679679729396725090681291)
    ·
      refine ⟨55019519594095087636021937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36679679729396725090681291 55019519594095087636021937)
      ·
        refine ⟨41264639695571315727016453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55019519594095087636021937 41264639695571315727016453)
        ·
          refine ⟨7737119942919621698815585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41264639695571315727016453 7737119942919621698815585)
          ·
            refine ⟨5802839957189716274111689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7737119942919621698815585 5802839957189716274111689)
            ·
              refine ⟨4352129967892287205583767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5802839957189716274111689 4352129967892287205583767)
              ·
                refine ⟨6528194951838430808375651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4352129967892287205583767 6528194951838430808375651)
                ·
                  refine ⟨9792292427757646212563477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6528194951838430808375651 9792292427757646212563477)
                  ·
                    refine ⟨459013707551139666213913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9792292427757646212563477 459013707551139666213913)
                    ·
                      rfl

theorem cell22_1340889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 6].length) (baseStart_1340889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1340889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1340889 prefixEnd_1340889 := by exact prefixLift 1340889
  have htrace : WordTrace (prefixWord ++ tailWord_1340889) baseStart_1340889 baseEnd_1340889 := by
    simpa [prefixWord, tailWord_1340889, baseEnd_1340889] using wordTrace_append hprefix tailTrace_1340889
  have hstable : (prefixWord ++ tailWord_1340889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340889).length < 2 ^ (prefixWord ++ tailWord_1340889).sum := by decide
  have hdescent : baseEnd_1340889 < baseStart_1340889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340893 : List Nat := [1, 4, 3, 1, 1, 2, 3, 3, 4]
def baseStart_1340893 : Nat := 118140960795 + 1340893 * 2 ^ 59
def prefixEnd_1340893 : Nat := 4983230072969 + 3 ^ 40 * 1340893 * 2
def baseEnd_1340893 : Nat := 153005025610961663037967

theorem tailTrace_1340893 : CollatzResearch.WordTrace tailWord_1340893 prefixEnd_1340893 153005025610961663037967 := by
  unfold tailWord_1340893
  simp only [CollatzResearch.WordTrace]
  refine ⟨48906385531181142137387333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32604257020787428091591555 48906385531181142137387333)
  ·
    refine ⟨9169947287096464150760125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48906385531181142137387333 9169947287096464150760125)
    ·
      refine ⟨3438730232661174056535047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9169947287096464150760125 3438730232661174056535047)
      ·
        refine ⟨5158095348991761084802571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3438730232661174056535047 5158095348991761084802571)
        ·
          refine ⟨7737143023487641627203857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5158095348991761084802571 7737143023487641627203857)
          ·
            refine ⟨5802857267615731220402893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7737143023487641627203857 5802857267615731220402893)
            ·
              refine ⟨2176071475355899207651085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5802857267615731220402893 2176071475355899207651085)
              ·
                refine ⟨816026803258462202869157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2176071475355899207651085 816026803258462202869157)
                ·
                  refine ⟨153005025610961663037967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 816026803258462202869157 153005025610961663037967)
                  ·
                    rfl

theorem cell22_1340893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 3, 4].length) (baseStart_1340893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1340893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1340893 prefixEnd_1340893 := by exact prefixLift 1340893
  have htrace : WordTrace (prefixWord ++ tailWord_1340893) baseStart_1340893 baseEnd_1340893 := by
    simpa [prefixWord, tailWord_1340893, baseEnd_1340893] using wordTrace_append hprefix tailTrace_1340893
  have hstable : (prefixWord ++ tailWord_1340893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340893).length < 2 ^ (prefixWord ++ tailWord_1340893).sum := by decide
  have hdescent : baseEnd_1340893 < baseStart_1340893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340925 : List Nat := [1, 4, 1, 1, 1, 6, 2, 1, 2, 3]
def baseStart_1340925 : Nat := 118140960795 + 1340925 * 2 ^ 59
def prefixEnd_1340925 : Nat := 4983230072969 + 3 ^ 40 * 1340925 * 2
def baseEnd_1340925 : Nat := 459026031086847572313803

theorem tailTrace_1340925 : CollatzResearch.WordTrace tailWord_1340925 prefixEnd_1340925 459026031086847572313803 := by
  unfold tailWord_1340925
  simp only [CollatzResearch.WordTrace]
  refine ⟨48907552667065211602552229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32605035111376807735034819 48907552667065211602552229)
  ·
    refine ⟨9170166125074727175478543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48907552667065211602552229 9170166125074727175478543)
    ·
      refine ⟨13755249187612090763217815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9170166125074727175478543 13755249187612090763217815)
      ·
        refine ⟨20632873781418136144826723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13755249187612090763217815 20632873781418136144826723)
        ·
          refine ⟨30949310672127204217240085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20632873781418136144826723 30949310672127204217240085)
          ·
            refine ⟨1450748937755962697683129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 30949310672127204217240085 1450748937755962697683129)
            ·
              refine ⟨1088061703316972023262347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1450748937755962697683129 1088061703316972023262347)
              ·
                refine ⟨1632092554975458034893521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1088061703316972023262347 1632092554975458034893521)
                ·
                  refine ⟨1224069416231593526170141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1632092554975458034893521 1224069416231593526170141)
                  ·
                    refine ⟨459026031086847572313803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1224069416231593526170141 459026031086847572313803)
                    ·
                      rfl

theorem cell22_1340925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2, 1, 2, 3].length) (baseStart_1340925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1340925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1340925 prefixEnd_1340925 := by exact prefixLift 1340925
  have htrace : WordTrace (prefixWord ++ tailWord_1340925) baseStart_1340925 baseEnd_1340925 := by
    simpa [prefixWord, tailWord_1340925, baseEnd_1340925] using wordTrace_append hprefix tailTrace_1340925
  have hstable : (prefixWord ++ tailWord_1340925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340925).length < 2 ^ (prefixWord ++ tailWord_1340925).sum := by decide
  have hdescent : baseEnd_1340925 < baseStart_1340925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340936 : List Nat := [2, 1, 3, 2, 1, 1, 2, 4, 3, 3]
def baseStart_1340936 : Nat := 118140960795 + 1340936 * 2 ^ 59
def prefixEnd_1340936 : Nat := 4983230072969 + 3 ^ 40 * 1340936 * 2
def baseEnd_1340936 : Nat := 459029796611647210288769

theorem tailTrace_1340936 : CollatzResearch.WordTrace tailWord_1340936 prefixEnd_1340936 459029796611647210288769 := by
  unfold tailWord_1340936
  simp only [CollatzResearch.WordTrace]
  refine ⟨24453976935012680240601331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32605302580016906987468441 24453976935012680240601331)
  ·
    refine ⟨36680965402519020360901997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24453976935012680240601331 36680965402519020360901997)
    ·
      refine ⟨13755362025944632635338249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36680965402519020360901997 13755362025944632635338249)
      ·
        refine ⟨10316521519458474476503687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13755362025944632635338249 10316521519458474476503687)
        ·
          refine ⟨15474782279187711714755531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10316521519458474476503687 15474782279187711714755531)
          ·
            refine ⟨23212173418781567572133297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15474782279187711714755531 23212173418781567572133297)
            ·
              refine ⟨17409130064086175679099973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23212173418781567572133297 17409130064086175679099973)
              ·
                refine ⟨3264211887016157939831245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17409130064086175679099973 3264211887016157939831245)
                ·
                  refine ⟨1224079457631059227436717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3264211887016157939831245 1224079457631059227436717)
                  ·
                    refine ⟨459029796611647210288769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1224079457631059227436717 459029796611647210288769)
                    ·
                      rfl

theorem cell22_1340936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4, 3, 3].length) (baseStart_1340936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1340936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1340936 prefixEnd_1340936 := by exact prefixLift 1340936
  have htrace : WordTrace (prefixWord ++ tailWord_1340936) baseStart_1340936 baseEnd_1340936 := by
    simpa [prefixWord, tailWord_1340936, baseEnd_1340936] using wordTrace_append hprefix tailTrace_1340936
  have hstable : (prefixWord ++ tailWord_1340936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340936).length < 2 ^ (prefixWord ++ tailWord_1340936).sum := by decide
  have hdescent : baseEnd_1340936 < baseStart_1340936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340970 : List Nat := [3, 1, 4, 1, 1, 1, 3, 4, 1, 3]
def baseStart_1340970 : Nat := 118140960795 + 1340970 * 2 ^ 59
def prefixEnd_1340970 : Nat := 4983230072969 + 3 ^ 40 * 1340970 * 2
def baseEnd_1340970 : Nat := 459041435506482454938665

theorem tailTrace_1340970 : CollatzResearch.WordTrace tailWord_1340970 prefixEnd_1340970 459041435506482454938665 := by
  unfold tailWord_1340970
  simp only [CollatzResearch.WordTrace]
  refine ⟨12227298487975546071985091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32606129301268122858626909 12227298487975546071985091)
  ·
    refine ⟨18340947731963319107977637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12227298487975546071985091 18340947731963319107977637)
    ·
      refine ⟨3438927699743122332745807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18340947731963319107977637 3438927699743122332745807)
      ·
        refine ⟨5158391549614683499118711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3438927699743122332745807 5158391549614683499118711)
        ·
          refine ⟨7737587324422025248678067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5158391549614683499118711 7737587324422025248678067)
          ·
            refine ⟨11606380986633037873017101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7737587324422025248678067 11606380986633037873017101)
            ·
              refine ⟨4352392869987389202381413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11606380986633037873017101 4352392869987389202381413)
              ·
                refine ⟨816073663122635475446515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4352392869987389202381413 816073663122635475446515)
                ·
                  refine ⟨1224110494683953213169773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 816073663122635475446515 1224110494683953213169773)
                  ·
                    refine ⟨459041435506482454938665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1224110494683953213169773 459041435506482454938665)
                    ·
                      rfl

theorem cell22_1340970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_1340970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1340970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1340970 prefixEnd_1340970 := by exact prefixLift 1340970
  have htrace : WordTrace (prefixWord ++ tailWord_1340970) baseStart_1340970 baseEnd_1340970 := by
    simpa [prefixWord, tailWord_1340970, baseEnd_1340970] using wordTrace_append hprefix tailTrace_1340970
  have hstable : (prefixWord ++ tailWord_1340970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340970).length < 2 ^ (prefixWord ++ tailWord_1340970).sum := by decide
  have hdescent : baseEnd_1340970 < baseStart_1340970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340981 : List Nat := [1, 3, 3, 1, 1, 4, 1, 1, 2, 5]
def baseStart_1340981 : Nat := 118140960795 + 1340981 * 2 ^ 59
def prefixEnd_1340981 : Nat := 4983230072969 + 3 ^ 40 * 1340981 * 2
def baseEnd_1340981 : Nat := 459045201031282092913631

theorem tailTrace_1340981 : CollatzResearch.WordTrace tailWord_1340981 prefixEnd_1340981 459045201031282092913631 := by
  unfold tailWord_1340981
  simp only [CollatzResearch.WordTrace]
  refine ⟨48909595154862333166590797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32606396769908222111060531 48909595154862333166590797)
  ·
    refine ⟨18341098183073374937471549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48909595154862333166590797 18341098183073374937471549)
    ·
      refine ⟨6877911818652515601551831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18341098183073374937471549 6877911818652515601551831)
      ·
        refine ⟨10316867727978773402327747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6877911818652515601551831 10316867727978773402327747)
        ·
          refine ⟨15475301591968160103491621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10316867727978773402327747 15475301591968160103491621)
          ·
            refine ⟨2901619048494030019404679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15475301591968160103491621 2901619048494030019404679)
            ·
              refine ⟨4352428572741045029107019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2901619048494030019404679 4352428572741045029107019)
              ·
                refine ⟨6528642859111567543660529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4352428572741045029107019 6528642859111567543660529)
                ·
                  refine ⟨4896482144333675657745397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6528642859111567543660529 4896482144333675657745397)
                  ·
                    refine ⟨459045201031282092913631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4896482144333675657745397 459045201031282092913631)
                    ·
                      rfl

theorem cell22_1340981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_1340981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1340981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1340981 prefixEnd_1340981 := by exact prefixLift 1340981
  have htrace : WordTrace (prefixWord ++ tailWord_1340981) baseStart_1340981 baseEnd_1340981 := by
    simpa [prefixWord, tailWord_1340981, baseEnd_1340981] using wordTrace_append hprefix tailTrace_1340981
  have hstable : (prefixWord ++ tailWord_1340981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340981).length < 2 ^ (prefixWord ++ tailWord_1340981).sum := by decide
  have hdescent : baseEnd_1340981 < baseStart_1340981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341028 : List Nat := [2, 3, 1, 1, 2, 3, 2, 4, 4]
def baseStart_1341028 : Nat := 118140960795 + 1341028 * 2 ^ 59
def prefixEnd_1341028 : Nat := 4983230072969 + 3 ^ 40 * 1341028 * 2
def baseEnd_1341028 : Nat := 153020430030596545662829

theorem tailTrace_1341028 : CollatzResearch.WordTrace tailWord_1341028 prefixEnd_1341028 153020430030596545662829 := by
  unfold tailWord_1341028
  simp only [CollatzResearch.WordTrace]
  refine ⟨24455654692846030096775869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32607539590461373462367825 24455654692846030096775869)
  ·
    refine ⟨9170870509817261286290951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24455654692846030096775869 9170870509817261286290951)
    ·
      refine ⟨13756305764725891929436427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9170870509817261286290951 13756305764725891929436427)
      ·
        refine ⟨20634458647088837894154641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13756305764725891929436427 20634458647088837894154641)
        ·
          refine ⟨15475843985316628420615981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20634458647088837894154641 15475843985316628420615981)
          ·
            refine ⟨5803441494493735657730993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15475843985316628420615981 5803441494493735657730993)
            ·
              refine ⟨4352581120870301743298245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5803441494493735657730993 4352581120870301743298245)
              ·
                refine ⟨816108960163181576868421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4352581120870301743298245 816108960163181576868421)
                ·
                  refine ⟨153020430030596545662829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 816108960163181576868421 153020430030596545662829)
                  ·
                    rfl

theorem cell22_1341028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 4, 4].length) (baseStart_1341028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1341028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1341028 prefixEnd_1341028 := by exact prefixLift 1341028
  have htrace : WordTrace (prefixWord ++ tailWord_1341028) baseStart_1341028 baseEnd_1341028 := by
    simpa [prefixWord, tailWord_1341028, baseEnd_1341028] using wordTrace_append hprefix tailTrace_1341028
  have hstable : (prefixWord ++ tailWord_1341028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341028).length < 2 ^ (prefixWord ++ tailWord_1341028).sum := by decide
  have hdescent : baseEnd_1341028 < baseStart_1341028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341039 : List Nat := [1, 1, 2, 1, 3, 2, 1, 11]
def baseStart_1341039 : Nat := 118140960795 + 1341039 * 2 ^ 59
def prefixEnd_1341039 : Nat := 4983230072969 + 3 ^ 40 * 1341039 * 2
def baseEnd_1341039 : Nat := 51007228401843252773717

theorem tailTrace_1341039 : CollatzResearch.WordTrace tailWord_1341039 prefixEnd_1341039 51007228401843252773717 := by
  unfold tailWord_1341039
  simp only [CollatzResearch.WordTrace]
  refine ⟨48911710588652209072202171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32607807059101472714801447 48911710588652209072202171)
  ·
    refine ⟨73367565882978313608303257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48911710588652209072202171 73367565882978313608303257)
    ·
      refine ⟨55025674412233735206227443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73367565882978313608303257 55025674412233735206227443)
      ·
        refine ⟨82538511618350602809341165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55025674412233735206227443 82538511618350602809341165)
        ·
          refine ⟨30951941856881476053502937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82538511618350602809341165 30951941856881476053502937)
          ·
            refine ⟨23213956392661107040127203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30951941856881476053502937 23213956392661107040127203)
            ·
              refine ⟨34820934588991660560190805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23213956392661107040127203 34820934588991660560190805)
              ·
                refine ⟨51007228401843252773717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 34820934588991660560190805 51007228401843252773717)
                ·
                  rfl

theorem cell22_1341039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 11].length) (baseStart_1341039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1341039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1341039 prefixEnd_1341039 := by exact prefixLift 1341039
  have htrace : WordTrace (prefixWord ++ tailWord_1341039) baseStart_1341039 baseEnd_1341039 := by
    simpa [prefixWord, tailWord_1341039, baseEnd_1341039] using wordTrace_append hprefix tailTrace_1341039
  have hstable : (prefixWord ++ tailWord_1341039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341039).length < 2 ^ (prefixWord ++ tailWord_1341039).sum := by decide
  have hdescent : baseEnd_1341039 < baseStart_1341039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341090 : List Nat := [3, 3, 1, 4, 1, 1, 2, 7]
def baseStart_1341090 : Nat := 118140960795 + 1341090 * 2 ^ 59
def prefixEnd_1341090 : Nat := 4983230072969 + 3 ^ 40 * 1341090 * 2
def baseEnd_1341090 : Nat := 51009168217649126882033

theorem tailTrace_1341090 : CollatzResearch.WordTrace tailWord_1341090 prefixEnd_1341090 51009168217649126882033 := by
  unfold tailWord_1341090
  simp only [CollatzResearch.WordTrace]
  refine ⟨12228392677866861195577181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32609047140978296521539149 12228392677866861195577181)
  ·
    refine ⟨4585647254200072948341443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12228392677866861195577181 4585647254200072948341443)
    ·
      refine ⟨6878470881300109422512165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4585647254200072948341443 6878470881300109422512165)
      ·
        refine ⟨1289713290243770516721031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6878470881300109422512165 1289713290243770516721031)
        ·
          refine ⟨1934569935365655775081547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1289713290243770516721031 1934569935365655775081547)
          ·
            refine ⟨2901854903048483662622321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1934569935365655775081547 2901854903048483662622321)
            ·
              refine ⟨2176391177286362746966741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2901854903048483662622321 2176391177286362746966741)
              ·
                refine ⟨51009168217649126882033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2176391177286362746966741 51009168217649126882033)
                ·
                  rfl

theorem cell22_1341090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 7].length) (baseStart_1341090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1341090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1341090 prefixEnd_1341090 := by exact prefixLift 1341090
  have htrace : WordTrace (prefixWord ++ tailWord_1341090) baseStart_1341090 baseEnd_1341090 := by
    simpa [prefixWord, tailWord_1341090, baseEnd_1341090] using wordTrace_append hprefix tailTrace_1341090
  have hstable : (prefixWord ++ tailWord_1341090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341090).length < 2 ^ (prefixWord ++ tailWord_1341090).sum := by decide
  have hdescent : baseEnd_1341090 < baseStart_1341090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341178 : List Nat := [3, 1, 1, 1, 1, 3, 1, 4, 4, 3]
def baseStart_1341178 : Nat := 118140960795 + 1341178 * 2 ^ 59
def prefixEnd_1341178 : Nat := 4983230072969 + 3 ^ 40 * 1341178 * 2
def baseEnd_1341178 : Nat := 459112638157239245738027

theorem tailTrace_1341178 : CollatzResearch.WordTrace tailWord_1341178 prefixEnd_1341178 459112638157239245738027 := by
  unfold tailWord_1341178
  simp only [CollatzResearch.WordTrace]
  refine ⟨12229195083787158952878047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32611186890099090541008125 12229195083787158952878047)
  ·
    refine ⟨18343792625680738429317071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12229195083787158952878047 18343792625680738429317071)
    ·
      refine ⟨27515688938521107643975607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18343792625680738429317071 27515688938521107643975607)
      ·
        refine ⟨41273533407781661465963411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27515688938521107643975607 41273533407781661465963411)
        ·
          refine ⟨61910300111672492198945117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41273533407781661465963411 61910300111672492198945117)
          ·
            refine ⟨23216362541877184574604419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61910300111672492198945117 23216362541877184574604419)
            ·
              refine ⟨34824543812815776861906629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23216362541877184574604419 34824543812815776861906629)
              ·
                refine ⟨6529601964902958161607493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34824543812815776861906629 6529601964902958161607493)
                ·
                  refine ⟨1224300368419304655301405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6529601964902958161607493 1224300368419304655301405)
                  ·
                    refine ⟨459112638157239245738027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1224300368419304655301405 459112638157239245738027)
                    ·
                      rfl

theorem cell22_1341178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 4, 3].length) (baseStart_1341178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1341178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1341178 prefixEnd_1341178 := by exact prefixLift 1341178
  have htrace : WordTrace (prefixWord ++ tailWord_1341178) baseStart_1341178 baseEnd_1341178 := by
    simpa [prefixWord, tailWord_1341178, baseEnd_1341178] using wordTrace_append hprefix tailTrace_1341178
  have hstable : (prefixWord ++ tailWord_1341178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341178).length < 2 ^ (prefixWord ++ tailWord_1341178).sum := by decide
  have hdescent : baseEnd_1341178 < baseStart_1341178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341180 : List Nat := [2, 2, 2, 1, 3, 1, 4, 3, 4]
def baseStart_1341180 : Nat := 118140960795 + 1341180 * 2 ^ 59
def prefixEnd_1341180 : Nat := 4983230072969 + 3 ^ 40 * 1341180 * 2
def baseEnd_1341180 : Nat := 153037774266037302396007

theorem tailTrace_1341180 : CollatzResearch.WordTrace tailWord_1341180 prefixEnd_1341180 153037774266037302396007 := by
  unfold tailWord_1341180
  simp only [CollatzResearch.WordTrace]
  refine ⟨24458426640570695076542497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32611235520760926768723329 24458426640570695076542497)
  ·
    refine ⟨18343819980428021307406873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24458426640570695076542497 18343819980428021307406873)
    ·
      refine ⟨13757864985321015980555155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18343819980428021307406873 13757864985321015980555155)
      ·
        refine ⟨20636797477981523970832733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13757864985321015980555155 20636797477981523970832733)
        ·
          refine ⟨7738799054243071489062275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20636797477981523970832733 7738799054243071489062275)
          ·
            refine ⟨11608198581364607233593413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7738799054243071489062275 11608198581364607233593413)
            ·
              refine ⟨2176537234005863856298765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11608198581364607233593413 2176537234005863856298765)
              ·
                refine ⟨816201462752198946112037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2176537234005863856298765 816201462752198946112037)
                ·
                  refine ⟨153037774266037302396007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 816201462752198946112037 153037774266037302396007)
                  ·
                    rfl

theorem cell22_1341180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 3, 4].length) (baseStart_1341180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1341180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1341180 prefixEnd_1341180 := by exact prefixLift 1341180
  have htrace : WordTrace (prefixWord ++ tailWord_1341180) baseStart_1341180 baseEnd_1341180 := by
    simpa [prefixWord, tailWord_1341180, baseEnd_1341180] using wordTrace_append hprefix tailTrace_1341180
  have hstable : (prefixWord ++ tailWord_1341180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341180).length < 2 ^ (prefixWord ++ tailWord_1341180).sum := by decide
  have hdescent : baseEnd_1341180 < baseStart_1341180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341182 : List Nat := [4, 2, 2, 1, 3, 1, 1, 3, 1, 4]
def baseStart_1341182 : Nat := 118140960795 + 1341182 * 2 ^ 59
def prefixEnd_1341182 : Nat := 4983230072969 + 3 ^ 40 * 1341182 * 2
def baseEnd_1341182 : Nat := 459114007438984568638015

theorem tailTrace_1341182 : CollatzResearch.WordTrace tailWord_1341182 prefixEnd_1341182 459114007438984568638015 := by
  unfold tailWord_1341182
  simp only [CollatzResearch.WordTrace]
  refine ⟨6114615778391768061832225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32611284151422762996438533 6114615778391768061832225)
  ·
    refine ⟨4585961833793826046374169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6114615778391768061832225 4585961833793826046374169)
    ·
      refine ⟨3439471375345369534780627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4585961833793826046374169 3439471375345369534780627)
      ·
        refine ⟨5159207063018054302170941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3439471375345369534780627 5159207063018054302170941)
        ·
          refine ⟨1934702648631770363314103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5159207063018054302170941 1934702648631770363314103)
          ·
            refine ⟨2902053972947655544971155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1934702648631770363314103 2902053972947655544971155)
            ·
              refine ⟨4353080959421483317456733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2902053972947655544971155 4353080959421483317456733)
              ·
                refine ⟨1632405359783056244046275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4353080959421483317456733 1632405359783056244046275)
                ·
                  refine ⟨2448608039674584366069413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1632405359783056244046275 2448608039674584366069413)
                  ·
                    refine ⟨459114007438984568638015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2448608039674584366069413 459114007438984568638015)
                    ·
                      rfl

theorem cell22_1341182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_1341182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1341182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1341182 prefixEnd_1341182 := by exact prefixLift 1341182
  have htrace : WordTrace (prefixWord ++ tailWord_1341182) baseStart_1341182 baseEnd_1341182 := by
    simpa [prefixWord, tailWord_1341182, baseEnd_1341182] using wordTrace_append hprefix tailTrace_1341182
  have hstable : (prefixWord ++ tailWord_1341182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341182).length < 2 ^ (prefixWord ++ tailWord_1341182).sum := by decide
  have hdescent : baseEnd_1341182 < baseStart_1341182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341195 : List Nat := [1, 1, 1, 1, 5, 1, 5, 2, 2, 3]
def baseStart_1341195 : Nat := 118140960795 + 1341195 * 2 ^ 59
def prefixEnd_1341195 : Nat := 4983230072969 + 3 ^ 40 * 1341195 * 2
def baseEnd_1341195 : Nat := 459118457604656868062975

theorem tailTrace_1341195 : CollatzResearch.WordTrace tailWord_1341195 prefixEnd_1341195 459118457604656868062975 := by
  unfold tailWord_1341195
  simp only [CollatzResearch.WordTrace]
  refine ⟨48917400376087047714881039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32611600250724698476587359 48917400376087047714881039)
  ·
    refine ⟨73376100564130571572321559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48917400376087047714881039 73376100564130571572321559)
    ·
      refine ⟨110064150846195857358482339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73376100564130571572321559 110064150846195857358482339)
      ·
        refine ⟨165096226269293786037723509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110064150846195857358482339 165096226269293786037723509)
        ·
          refine ⟨15477771212746292441036579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 165096226269293786037723509 15477771212746292441036579)
          ·
            refine ⟨23216656819119438661554869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15477771212746292441036579 23216656819119438661554869)
            ·
              refine ⟨2176561576792447374520769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23216656819119438661554869 2176561576792447374520769)
              ·
                refine ⟨1632421182594335530890577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2176561576792447374520769 1632421182594335530890577)
                ·
                  refine ⟨1224315886945751648167933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1632421182594335530890577 1224315886945751648167933)
                  ·
                    refine ⟨459118457604656868062975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1224315886945751648167933 459118457604656868062975)
                    ·
                      rfl

theorem cell22_1341195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 2, 2, 3].length) (baseStart_1341195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1341195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1341195 prefixEnd_1341195 := by exact prefixLift 1341195
  have htrace : WordTrace (prefixWord ++ tailWord_1341195) baseStart_1341195 baseEnd_1341195 := by
    simpa [prefixWord, tailWord_1341195, baseEnd_1341195] using wordTrace_append hprefix tailTrace_1341195
  have hstable : (prefixWord ++ tailWord_1341195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341195).length < 2 ^ (prefixWord ++ tailWord_1341195).sum := by decide
  have hdescent : baseEnd_1341195 < baseStart_1341195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341212 : List Nat := [2, 2, 3, 1, 1, 2, 5, 1, 2, 3]
def baseStart_1341212 : Nat := 118140960795 + 1341212 * 2 ^ 59
def prefixEnd_1341212 : Nat := 4983230072969 + 3 ^ 40 * 1341212 * 2
def baseEnd_1341212 : Nat := 459124277052074490387923

theorem tailTrace_1341212 : CollatzResearch.WordTrace tailWord_1341212 prefixEnd_1341212 459124277052074490387923 := by
  unfold tailWord_1341212
  simp only [CollatzResearch.WordTrace]
  refine ⟨24459010208512729809124945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32612013611350306412166593 24459010208512729809124945)
  ·
    refine ⟨18344257656384547356843709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24459010208512729809124945 18344257656384547356843709)
    ·
      refine ⟨6879096621144205258816391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18344257656384547356843709 6879096621144205258816391)
      ·
        refine ⟨10318644931716307888224587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6879096621144205258816391 10318644931716307888224587)
        ·
          refine ⟨15477967397574461832336881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10318644931716307888224587 15477967397574461832336881)
          ·
            refine ⟨11608475548180846374252661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15477967397574461832336881 11608475548180846374252661)
            ·
              refine ⟨1088294582641954347586187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11608475548180846374252661 1088294582641954347586187)
              ·
                refine ⟨1632441873962931521379281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1088294582641954347586187 1632441873962931521379281)
                ·
                  refine ⟨1224331405472198641034461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1632441873962931521379281 1224331405472198641034461)
                  ·
                    refine ⟨459124277052074490387923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1224331405472198641034461 459124277052074490387923)
                    ·
                      rfl

theorem cell22_1341212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5, 1, 2, 3].length) (baseStart_1341212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1341212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1341212 prefixEnd_1341212 := by exact prefixLift 1341212
  have htrace : WordTrace (prefixWord ++ tailWord_1341212) baseStart_1341212 baseEnd_1341212 := by
    simpa [prefixWord, tailWord_1341212, baseEnd_1341212] using wordTrace_append hprefix tailTrace_1341212
  have hstable : (prefixWord ++ tailWord_1341212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341212).length < 2 ^ (prefixWord ++ tailWord_1341212).sum := by decide
  have hdescent : baseEnd_1341212 < baseStart_1341212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341253 : List Nat := [1, 3, 1, 1, 1, 2, 4, 4, 5]
def baseStart_1341253 : Nat := 118140960795 + 1341253 * 2 ^ 59
def prefixEnd_1341253 : Nat := 4983230072969 + 3 ^ 40 * 1341253 * 2
def baseEnd_1341253 : Nat := 153046104063321350037599

theorem tailTrace_1341253 : CollatzResearch.WordTrace tailWord_1341253 prefixEnd_1341253 153046104063321350037599 := by
  unfold tailWord_1341253
  simp only [CollatzResearch.WordTrace]
  refine ⟨48919515809876923620492413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32613010539917949080328275 48919515809876923620492413)
  ·
    refine ⟨18344818428703846357684655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48919515809876923620492413 18344818428703846357684655)
    ·
      refine ⟨27517227643055769536526983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18344818428703846357684655 27517227643055769536526983)
      ·
        refine ⟨41275841464583654304790475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27517227643055769536526983 41275841464583654304790475)
        ·
          refine ⟨61913762196875481457185713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41275841464583654304790475 61913762196875481457185713)
          ·
            refine ⟨46435321647656611092889285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61913762196875481457185713 46435321647656611092889285)
            ·
              refine ⟨8706622808935614579916741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46435321647656611092889285 8706622808935614579916741)
              ·
                refine ⟨1632491776675427733734389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8706622808935614579916741 1632491776675427733734389)
                ·
                  refine ⟨153046104063321350037599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1632491776675427733734389 153046104063321350037599)
                  ·
                    rfl

theorem cell22_1341253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 4, 5].length) (baseStart_1341253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1341253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1341253 prefixEnd_1341253 := by exact prefixLift 1341253
  have htrace : WordTrace (prefixWord ++ tailWord_1341253) baseStart_1341253 baseEnd_1341253 := by
    simpa [prefixWord, tailWord_1341253, baseEnd_1341253] using wordTrace_append hprefix tailTrace_1341253
  have hstable : (prefixWord ++ tailWord_1341253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341253).length < 2 ^ (prefixWord ++ tailWord_1341253).sum := by decide
  have hdescent : baseEnd_1341253 < baseStart_1341253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341328 : List Nat := [2, 1, 1, 1, 1, 1, 2, 3, 6, 4]
def baseStart_1341328 : Nat := 118140960795 + 1341328 * 2 ^ 59
def prefixEnd_1341328 : Nat := 4983230072969 + 3 ^ 40 * 1341328 * 2
def baseEnd_1341328 : Nat := 459163986222688854487567

theorem tailTrace_1341328 : CollatzResearch.WordTrace tailWord_1341328 prefixEnd_1341328 459163986222688854487567 := by
  unfold tailWord_1341328
  simp only [CollatzResearch.WordTrace]
  refine ⟨24461125642302605714736319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32614834189736807619648425 24461125642302605714736319)
  ·
    refine ⟨36691688463453908572104479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24461125642302605714736319 36691688463453908572104479)
    ·
      refine ⟨55037532695180862858156719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36691688463453908572104479 55037532695180862858156719)
      ·
        refine ⟨82556299042771294287235079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55037532695180862858156719 82556299042771294287235079)
        ·
          refine ⟨123834448564156941430852619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82556299042771294287235079 123834448564156941430852619)
          ·
            refine ⟨185751672846235412146278929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123834448564156941430852619 185751672846235412146278929)
            ·
              refine ⟨139313754634676559109709197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185751672846235412146278929 139313754634676559109709197)
              ·
                refine ⟨52242657988003709666140949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 139313754634676559109709197 52242657988003709666140949)
                ·
                  refine ⟨2448874593187673890600357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 52242657988003709666140949 2448874593187673890600357)
                  ·
                    refine ⟨459163986222688854487567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2448874593187673890600357 459163986222688854487567)
                    ·
                      rfl

theorem cell22_1341328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 6, 4].length) (baseStart_1341328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1341328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1341328 prefixEnd_1341328 := by exact prefixLift 1341328
  have htrace : WordTrace (prefixWord ++ tailWord_1341328) baseStart_1341328 baseEnd_1341328 := by
    simpa [prefixWord, tailWord_1341328, baseEnd_1341328] using wordTrace_append hprefix tailTrace_1341328
  have hstable : (prefixWord ++ tailWord_1341328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341328).length < 2 ^ (prefixWord ++ tailWord_1341328).sum := by decide
  have hdescent : baseEnd_1341328 < baseStart_1341328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341394 : List Nat := [3, 2, 2, 3, 2, 2, 2, 6]
def baseStart_1341394 : Nat := 118140960795 + 1341394 * 2 ^ 59
def prefixEnd_1341394 : Nat := 4983230072969 + 3 ^ 40 * 1341394 * 2
def baseEnd_1341394 : Nat := 51020731041276298037485

theorem tailTrace_1341394 : CollatzResearch.WordTrace tailWord_1341394 prefixEnd_1341394 51020731041276298037485 := by
  unfold tailWord_1341394
  simp only [CollatzResearch.WordTrace]
  refine ⟨12231164625591526175343809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32616439001577403134250157 12231164625591526175343809)
  ·
    refine ⟨9173373469193644631507857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12231164625591526175343809 9173373469193644631507857)
    ·
      refine ⟨6880030101895233473630893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9173373469193644631507857 6880030101895233473630893)
      ·
        refine ⟨2580011288210712552611585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6880030101895233473630893 2580011288210712552611585)
        ·
          refine ⟨1935008466158034414458689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2580011288210712552611585 1935008466158034414458689)
          ·
            refine ⟨1451256349618525810844017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1935008466158034414458689 1451256349618525810844017)
            ·
              refine ⟨1088442262213894358133013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1451256349618525810844017 1088442262213894358133013)
              ·
                refine ⟨51020731041276298037485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1088442262213894358133013 51020731041276298037485)
                ·
                  rfl

theorem cell22_1341394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2, 6].length) (baseStart_1341394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1341394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1341394 prefixEnd_1341394 := by exact prefixLift 1341394
  have htrace : WordTrace (prefixWord ++ tailWord_1341394) baseStart_1341394 baseEnd_1341394 := by
    simpa [prefixWord, tailWord_1341394, baseEnd_1341394] using wordTrace_append hprefix tailTrace_1341394
  have hstable : (prefixWord ++ tailWord_1341394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341394).length < 2 ^ (prefixWord ++ tailWord_1341394).sum := by decide
  have hdescent : baseEnd_1341394 < baseStart_1341394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341409 : List Nat := [1, 2, 3, 1, 2, 1, 5, 3, 1, 3]
def baseStart_1341409 : Nat := 118140960795 + 1341409 * 2 ^ 59
def prefixEnd_1341409 : Nat := 4983230072969 + 3 ^ 40 * 1341409 * 2
def baseEnd_1341409 : Nat := 459191714178031643212319

theorem tailTrace_1341409 : CollatzResearch.WordTrace tailWord_1341409 prefixEnd_1341409 459191714178031643212319 := by
  unfold tailWord_1341409
  simp only [CollatzResearch.WordTrace]
  refine ⟨48925205597311762263171281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32616803731541174842114187 48925205597311762263171281)
  ·
    refine ⟨36693904197983821697378461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48925205597311762263171281 36693904197983821697378461)
    ·
      refine ⟨13760214074243933136516923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36693904197983821697378461 13760214074243933136516923)
      ·
        refine ⟨20640321111365899704775385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13760214074243933136516923 20640321111365899704775385)
        ·
          refine ⟨15480240833524424778581539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20640321111365899704775385 15480240833524424778581539)
          ·
            refine ⟨23220361250286637167872309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15480240833524424778581539 23220361250286637167872309)
            ·
              refine ⟨2176908867214372234488029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23220361250286637167872309 2176908867214372234488029)
              ·
                refine ⟨816340825205389587933011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2176908867214372234488029 816340825205389587933011)
                ·
                  refine ⟨1224511237808084381899517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 816340825205389587933011 1224511237808084381899517)
                  ·
                    refine ⟨459191714178031643212319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1224511237808084381899517 459191714178031643212319)
                    ·
                      rfl

theorem cell22_1341409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 3, 1, 3].length) (baseStart_1341409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1341409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1341409 prefixEnd_1341409 := by exact prefixLift 1341409
  have htrace : WordTrace (prefixWord ++ tailWord_1341409) baseStart_1341409 baseEnd_1341409 := by
    simpa [prefixWord, tailWord_1341409, baseEnd_1341409] using wordTrace_append hprefix tailTrace_1341409
  have hstable : (prefixWord ++ tailWord_1341409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341409).length < 2 ^ (prefixWord ++ tailWord_1341409).sum := by decide
  have hdescent : baseEnd_1341409 < baseStart_1341409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341495 : List Nat := [1, 1, 3, 1, 2, 2, 5, 7]
def baseStart_1341495 : Nat := 118140960795 + 1341495 * 2 ^ 59
def prefixEnd_1341495 : Nat := 4983230072969 + 3 ^ 40 * 1341495 * 2
def baseEnd_1341495 : Nat := 51024572637284009506895

theorem tailTrace_1341495 : CollatzResearch.WordTrace tailWord_1341495 prefixEnd_1341495 51024572637284009506895 := by
  unfold tailWord_1341495
  simp only [CollatzResearch.WordTrace]
  refine ⟨48928342275000198950801939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32618894850000132633867959 48928342275000198950801939)
  ·
    refine ⟨73392513412500298426202909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48928342275000198950801939 73392513412500298426202909)
    ·
      refine ⟨27522192529687611909826091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73392513412500298426202909 27522192529687611909826091)
      ·
        refine ⟨41283288794531417864739137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27522192529687611909826091 41283288794531417864739137)
        ·
          refine ⟨30962466595898563398554353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41283288794531417864739137 30962466595898563398554353)
          ·
            refine ⟨23221849946923922548915765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30962466595898563398554353 23221849946923922548915765)
            ·
              refine ⟨2177048432524117738960853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23221849946923922548915765 2177048432524117738960853)
              ·
                refine ⟨51024572637284009506895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2177048432524117738960853 51024572637284009506895)
                ·
                  rfl

theorem cell22_1341495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 7].length) (baseStart_1341495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1341495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1341495 prefixEnd_1341495 := by exact prefixLift 1341495
  have htrace : WordTrace (prefixWord ++ tailWord_1341495) baseStart_1341495 baseEnd_1341495 := by
    simpa [prefixWord, tailWord_1341495, baseEnd_1341495] using wordTrace_append hprefix tailTrace_1341495
  have hstable : (prefixWord ++ tailWord_1341495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341495).length < 2 ^ (prefixWord ++ tailWord_1341495).sum := by decide
  have hdescent : baseEnd_1341495 < baseStart_1341495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341533 : List Nat := [1, 4, 4, 1, 1, 3, 1, 2, 2, 3]
def baseStart_1341533 : Nat := 118140960795 + 1341533 * 2 ^ 59
def prefixEnd_1341533 : Nat := 4983230072969 + 3 ^ 40 * 1341533 * 2
def baseEnd_1341533 : Nat := 459234161912136653111939

theorem tailTrace_1341533 : CollatzResearch.WordTrace tailWord_1341533 prefixEnd_1341533 459234161912136653111939 := by
  unfold tailWord_1341533
  simp only [CollatzResearch.WordTrace]
  refine ⟨48929728248862531440685253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32619818832575020960456835 48929728248862531440685253)
  ·
    refine ⟨9174324046661724645128485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48929728248862531440685253 9174324046661724645128485)
    ·
      refine ⟨1720185758749073370961591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9174324046661724645128485 1720185758749073370961591)
      ·
        refine ⟨2580278638123610056442387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1720185758749073370961591 2580278638123610056442387)
        ·
          refine ⟨3870417957185415084663581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2580278638123610056442387 3870417957185415084663581)
          ·
            refine ⟨1451406733944530656748843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3870417957185415084663581 1451406733944530656748843)
            ·
              refine ⟨2177110100916795985123265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1451406733944530656748843 2177110100916795985123265)
              ·
                refine ⟨1632832575687596988842449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2177110100916795985123265 1632832575687596988842449)
                ·
                  refine ⟨1224624431765697741631837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1632832575687596988842449 1224624431765697741631837)
                  ·
                    refine ⟨459234161912136653111939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1224624431765697741631837 459234161912136653111939)
                    ·
                      rfl

theorem cell22_1341533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_1341533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1341533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1341533 prefixEnd_1341533 := by exact prefixLift 1341533
  have htrace : WordTrace (prefixWord ++ tailWord_1341533) baseStart_1341533 baseEnd_1341533 := by
    simpa [prefixWord, tailWord_1341533, baseEnd_1341533] using wordTrace_append hprefix tailTrace_1341533
  have hstable : (prefixWord ++ tailWord_1341533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341533).length < 2 ^ (prefixWord ++ tailWord_1341533).sum := by decide
  have hdescent : baseEnd_1341533 < baseStart_1341533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341578 : List Nat := [3, 1, 2, 3, 1, 4, 1, 3, 1, 3]
def baseStart_1341578 : Nat := 118140960795 + 1341578 * 2 ^ 59
def prefixEnd_1341578 : Nat := 4983230072969 + 3 ^ 40 * 1341578 * 2
def baseEnd_1341578 : Nat := 459249566331771535736801

theorem tailTrace_1341578 : CollatzResearch.WordTrace tailWord_1341578 prefixEnd_1341578 459249566331771535736801 := by
  unfold tailWord_1341578
  simp only [CollatzResearch.WordTrace]
  refine ⟨12232842383424876031518347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32620913022466336084048925 12232842383424876031518347)
  ·
    refine ⟨18349263575137314047277521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12232842383424876031518347 18349263575137314047277521)
    ·
      refine ⟨13761947681352985535458141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18349263575137314047277521 13761947681352985535458141)
      ·
        refine ⟨5160730380507369575796803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13761947681352985535458141 5160730380507369575796803)
        ·
          refine ⟨7741095570761054363695205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5160730380507369575796803 7741095570761054363695205)
          ·
            refine ⟨1451455419517697693192851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7741095570761054363695205 1451455419517697693192851)
            ·
              refine ⟨2177183129276546539789277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1451455419517697693192851 2177183129276546539789277)
              ·
                refine ⟨816443673478704952420979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2177183129276546539789277 816443673478704952420979)
                ·
                  refine ⟨1224665510218057428631469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 816443673478704952420979 1224665510218057428631469)
                  ·
                    refine ⟨459249566331771535736801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1224665510218057428631469 459249566331771535736801)
                    ·
                      rfl

theorem cell22_1341578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 3, 1, 3].length) (baseStart_1341578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1341578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1341578 prefixEnd_1341578 := by exact prefixLift 1341578
  have htrace : WordTrace (prefixWord ++ tailWord_1341578) baseStart_1341578 baseEnd_1341578 := by
    simpa [prefixWord, tailWord_1341578, baseEnd_1341578] using wordTrace_append hprefix tailTrace_1341578
  have hstable : (prefixWord ++ tailWord_1341578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341578).length < 2 ^ (prefixWord ++ tailWord_1341578).sum := by decide
  have hdescent : baseEnd_1341578 < baseStart_1341578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341621 : List Nat := [1, 3, 3, 4, 1, 1, 1, 1, 3, 4]
def baseStart_1341621 : Nat := 118140960795 + 1341621 * 2 ^ 59
def prefixEnd_1341621 : Nat := 4983230072969 + 3 ^ 40 * 1341621 * 2
def baseEnd_1341621 : Nat := 459264286110533756911669

theorem tailTrace_1341621 : CollatzResearch.WordTrace tailWord_1341621 prefixEnd_1341621 459264286110533756911669 := by
  unfold tailWord_1341621
  simp only [CollatzResearch.WordTrace]
  refine ⟨48932937872543722469888717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32621958581695814979925811 48932937872543722469888717)
  ·
    refine ⟨18349851702203895926208269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48932937872543722469888717 18349851702203895926208269)
    ·
      refine ⟨6881194388326460972328101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18349851702203895926208269 6881194388326460972328101)
      ·
        refine ⟨1290223947811211432311519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6881194388326460972328101 1290223947811211432311519)
        ·
          refine ⟨1935335921716817148467279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1290223947811211432311519 1935335921716817148467279)
          ·
            refine ⟨2903003882575225722700919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1935335921716817148467279 2903003882575225722700919)
            ·
              refine ⟨4354505823862838584051379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2903003882575225722700919 4354505823862838584051379)
              ·
                refine ⟨6531758735794257876077069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4354505823862838584051379 6531758735794257876077069)
                ·
                  refine ⟨2449409525922846703528901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6531758735794257876077069 2449409525922846703528901)
                  ·
                    refine ⟨459264286110533756911669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2449409525922846703528901 459264286110533756911669)
                    ·
                      rfl

theorem cell22_1341621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_1341621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1341621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1341621 prefixEnd_1341621 := by exact prefixLift 1341621
  have htrace : WordTrace (prefixWord ++ tailWord_1341621) baseStart_1341621 baseEnd_1341621 := by
    simpa [prefixWord, tailWord_1341621, baseEnd_1341621] using wordTrace_append hprefix tailTrace_1341621
  have hstable : (prefixWord ++ tailWord_1341621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341621).length < 2 ^ (prefixWord ++ tailWord_1341621).sum := by decide
  have hdescent : baseEnd_1341621 < baseStart_1341621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341679 : List Nat := [1, 1, 2, 1, 6, 1, 1, 1, 5, 3]
def baseStart_1341679 : Nat := 118140960795 + 1341679 * 2 ^ 59
def prefixEnd_1341679 : Nat := 4983230072969 + 3 ^ 40 * 1341679 * 2
def baseEnd_1341679 : Nat := 459284140695840938961491

theorem tailTrace_1341679 : CollatzResearch.WordTrace tailWord_1341679 prefixEnd_1341679 459284140695840938961491 := by
  unfold tailWord_1341679
  simp only [CollatzResearch.WordTrace]
  refine ⟨48935053306333598375500091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32623368870889065583666727 48935053306333598375500091)
  ·
    refine ⟨73402579959500397563250137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48935053306333598375500091 73402579959500397563250137)
    ·
      refine ⟨55051934969625298172437603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73402579959500397563250137 55051934969625298172437603)
      ·
        refine ⟨82577902454437947258656405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55051934969625298172437603 82577902454437947258656405)
        ·
          refine ⟨3870839177551778777749519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 82577902454437947258656405 3870839177551778777749519)
          ·
            refine ⟨5806258766327668166624279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3870839177551778777749519 5806258766327668166624279)
            ·
              refine ⟨8709388149491502249936419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5806258766327668166624279 8709388149491502249936419)
              ·
                refine ⟨13064082224237253374904629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8709388149491502249936419 13064082224237253374904629)
                ·
                  refine ⟨1224757708522242503897309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13064082224237253374904629 1224757708522242503897309)
                  ·
                    refine ⟨459284140695840938961491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1224757708522242503897309 459284140695840938961491)
                    ·
                      rfl

theorem cell22_1341679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 5, 3].length) (baseStart_1341679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1341679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1341679 prefixEnd_1341679 := by exact prefixLift 1341679
  have htrace : WordTrace (prefixWord ++ tailWord_1341679) baseStart_1341679 baseEnd_1341679 := by
    simpa [prefixWord, tailWord_1341679, baseEnd_1341679] using wordTrace_append hprefix tailTrace_1341679
  have hstable : (prefixWord ++ tailWord_1341679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341679).length < 2 ^ (prefixWord ++ tailWord_1341679).sum := by decide
  have hdescent : baseEnd_1341679 < baseStart_1341679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341696 : List Nat := [2, 1, 1, 2, 1, 1, 5, 5, 1, 3]
def baseStart_1341696 : Nat := 118140960795 + 1341696 * 2 ^ 59
def prefixEnd_1341696 : Nat := 4983230072969 + 3 ^ 40 * 1341696 * 2
def baseEnd_1341696 : Nat := 459289960143258561286439

theorem tailTrace_1341696 : CollatzResearch.WordTrace tailWord_1341696 prefixEnd_1341696 459289960143258561286439 := by
  unfold tailWord_1341696
  simp only [CollatzResearch.WordTrace]
  refine ⟨24467836673636005139434471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32623782231514673519245961 24467836673636005139434471)
  ·
    refine ⟨36701755010454007709151707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24467836673636005139434471 36701755010454007709151707)
    ·
      refine ⟨55052632515681011563727561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36701755010454007709151707 55052632515681011563727561)
      ·
        refine ⟨41289474386760758672795671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55052632515681011563727561 41289474386760758672795671)
        ·
          refine ⟨61934211580141138009193507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41289474386760758672795671 61934211580141138009193507)
          ·
            refine ⟨92901317370211707013790261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61934211580141138009193507 92901317370211707013790261)
            ·
              refine ⟨8709498503457347532542837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 92901317370211707013790261 8709498503457347532542837)
              ·
                refine ⟨816515484699126331175891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8709498503457347532542837 816515484699126331175891)
                ·
                  refine ⟨1224773227048689496763837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 816515484699126331175891 1224773227048689496763837)
                  ·
                    refine ⟨459289960143258561286439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1224773227048689496763837 459289960143258561286439)
                    ·
                      rfl

theorem cell22_1341696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 5, 1, 3].length) (baseStart_1341696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1341696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1341696 prefixEnd_1341696 := by exact prefixLift 1341696
  have htrace : WordTrace (prefixWord ++ tailWord_1341696) baseStart_1341696 baseEnd_1341696 := by
    simpa [prefixWord, tailWord_1341696, baseEnd_1341696] using wordTrace_append hprefix tailTrace_1341696
  have hstable : (prefixWord ++ tailWord_1341696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341696).length < 2 ^ (prefixWord ++ tailWord_1341696).sum := by decide
  have hdescent : baseEnd_1341696 < baseStart_1341696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341707 : List Nat := [1, 1, 1, 1, 5, 2, 1, 1, 4, 5]
def baseStart_1341707 : Nat := 118140960795 + 1341707 * 2 ^ 59
def prefixEnd_1341707 : Nat := 4983230072969 + 3 ^ 40 * 1341707 * 2
def baseEnd_1341707 : Nat := 459293725668058199261405

theorem tailTrace_1341707 : CollatzResearch.WordTrace tailWord_1341707 prefixEnd_1341707 459293725668058199261405 := by
  unfold tailWord_1341707
  simp only [CollatzResearch.WordTrace]
  refine ⟨48936074550232159157519375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32624049700154772771679583 48936074550232159157519375)
  ·
    refine ⟨73404111825348238736279063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48936074550232159157519375 73404111825348238736279063)
    ·
      refine ⟨110106167738022358104418595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73404111825348238736279063 110106167738022358104418595)
      ·
        refine ⟨165159251607033537156627893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110106167738022358104418595 165159251607033537156627893)
        ·
          refine ⟨15483679838159394108433865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 165159251607033537156627893 15483679838159394108433865)
          ·
            refine ⟨11612759878619545581325399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15483679838159394108433865 11612759878619545581325399)
            ·
              refine ⟨17419139817929318371988099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11612759878619545581325399 17419139817929318371988099)
              ·
                refine ⟨26128709726893977557982149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17419139817929318371988099 26128709726893977557982149)
                ·
                  refine ⟨4899133073792620792121653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26128709726893977557982149 4899133073792620792121653)
                  ·
                    refine ⟨459293725668058199261405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4899133073792620792121653 459293725668058199261405)
                    ·
                      rfl

theorem cell22_1341707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 4, 5].length) (baseStart_1341707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1341707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1341707 prefixEnd_1341707 := by exact prefixLift 1341707
  have htrace : WordTrace (prefixWord ++ tailWord_1341707) baseStart_1341707 baseEnd_1341707 := by
    simpa [prefixWord, tailWord_1341707, baseEnd_1341707] using wordTrace_append hprefix tailTrace_1341707
  have hstable : (prefixWord ++ tailWord_1341707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341707).length < 2 ^ (prefixWord ++ tailWord_1341707).sum := by decide
  have hdescent : baseEnd_1341707 < baseStart_1341707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341799 : List Nat := [1, 1, 5, 1, 3, 1, 2, 8]
def baseStart_1341799 : Nat := 118140960795 + 1341799 * 2 ^ 59
def prefixEnd_1341799 : Nat := 4983230072969 + 3 ^ 40 * 1341799 * 2
def baseEnd_1341799 : Nat := 51036135460911180662347

theorem tailTrace_1341799 : CollatzResearch.WordTrace tailWord_1341799 prefixEnd_1341799 51036135460911180662347 := by
  unfold tailWord_1341799
  simp only [CollatzResearch.WordTrace]
  refine ⟨48939430065898858869868451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32626286710599239246578967 48939430065898858869868451)
  ·
    refine ⟨73409145098848288304802677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48939430065898858869868451 73409145098848288304802677)
    ·
      refine ⟨6882107353017027028575251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73409145098848288304802677 6882107353017027028575251)
      ·
        refine ⟨10323161029525540542862877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6882107353017027028575251 10323161029525540542862877)
        ·
          refine ⟨3871185386072077703573579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10323161029525540542862877 3871185386072077703573579)
          ·
            refine ⟨5806778079108116555360369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3871185386072077703573579 5806778079108116555360369)
            ·
              refine ⟨4355083559331087416520277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5806778079108116555360369 4355083559331087416520277)
              ·
                refine ⟨51036135460911180662347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4355083559331087416520277 51036135460911180662347)
                ·
                  rfl

theorem cell22_1341799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 8].length) (baseStart_1341799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1341799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1341799 prefixEnd_1341799 := by exact prefixLift 1341799
  have htrace : WordTrace (prefixWord ++ tailWord_1341799) baseStart_1341799 baseEnd_1341799 := by
    simpa [prefixWord, tailWord_1341799, baseEnd_1341799] using wordTrace_append hprefix tailTrace_1341799
  have hstable : (prefixWord ++ tailWord_1341799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341799).length < 2 ^ (prefixWord ++ tailWord_1341799).sum := by decide
  have hdescent : baseEnd_1341799 < baseStart_1341799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341831 : List Nat := [1, 1, 4, 2, 2, 1, 2, 3, 3, 3]
def baseStart_1341831 : Nat := 118140960795 + 1341831 * 2 ^ 59
def prefixEnd_1341831 : Nat := 4983230072969 + 3 ^ 40 * 1341831 * 2
def baseEnd_1341831 : Nat := 459336173402163209161025

theorem tailTrace_1341831 : CollatzResearch.WordTrace tailWord_1341831 prefixEnd_1341831 459336173402163209161025 := by
  unfold tailWord_1341831
  simp only [CollatzResearch.WordTrace]
  refine ⟨48940597201782928335033347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32627064801188618890022231 48940597201782928335033347)
  ·
    refine ⟨73410895802674392502550021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48940597201782928335033347 73410895802674392502550021)
    ·
      refine ⟨13764542963001448594228129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73410895802674392502550021 13764542963001448594228129)
      ·
        refine ⟨10323407222251086445671097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13764542963001448594228129 10323407222251086445671097)
        ·
          refine ⟨7742555416688314834253323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10323407222251086445671097 7742555416688314834253323)
          ·
            refine ⟨11613833125032472251379985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7742555416688314834253323 11613833125032472251379985)
            ·
              refine ⟨8710374843774354188534989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11613833125032472251379985 8710374843774354188534989)
              ·
                refine ⟨3266390566415382820700621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8710374843774354188534989 3266390566415382820700621)
                ·
                  refine ⟨1224896462405768557762733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3266390566415382820700621 1224896462405768557762733)
                  ·
                    refine ⟨459336173402163209161025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1224896462405768557762733 459336173402163209161025)
                    ·
                      rfl

theorem cell22_1341831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 3, 3, 3].length) (baseStart_1341831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1341831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1341831 prefixEnd_1341831 := by exact prefixLift 1341831
  have htrace : WordTrace (prefixWord ++ tailWord_1341831) baseStart_1341831 baseEnd_1341831 := by
    simpa [prefixWord, tailWord_1341831, baseEnd_1341831] using wordTrace_append hprefix tailTrace_1341831
  have hstable : (prefixWord ++ tailWord_1341831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341831).length < 2 ^ (prefixWord ++ tailWord_1341831).sum := by decide
  have hdescent : baseEnd_1341831 < baseStart_1341831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341848 : List Nat := [2, 1, 2, 5, 1, 2, 1, 2, 3, 3]
def baseStart_1341848 : Nat := 118140960795 + 1341848 * 2 ^ 59
def prefixEnd_1341848 : Nat := 4983230072969 + 3 ^ 40 * 1341848 * 2
def baseEnd_1341848 : Nat := 459341992849580831485973

theorem tailTrace_1341848 : CollatzResearch.WordTrace tailWord_1341848 prefixEnd_1341848 459341992849580831485973 := by
  unfold tailWord_1341848
  simp only [CollatzResearch.WordTrace]
  refine ⟨24470608621360670119201099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32627478161814226825601465 24470608621360670119201099)
  ·
    refine ⟨36705912932041005178801649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24470608621360670119201099 36705912932041005178801649)
    ·
      refine ⟨27529434699030753884101237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36705912932041005178801649 27529434699030753884101237)
      ·
        refine ⟨2580884503034133176634491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27529434699030753884101237 2580884503034133176634491)
        ·
          refine ⟨3871326754551199764951737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2580884503034133176634491 3871326754551199764951737)
          ·
            refine ⟨2903495065913399823713803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3871326754551199764951737 2903495065913399823713803)
            ·
              refine ⟨4355242598870099735570705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2903495065913399823713803 4355242598870099735570705)
              ·
                refine ⟨3266431949152574801678029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4355242598870099735570705 3266431949152574801678029)
                ·
                  refine ⟨1224911980932215550629261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3266431949152574801678029 1224911980932215550629261)
                  ·
                    refine ⟨459341992849580831485973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1224911980932215550629261 459341992849580831485973)
                    ·
                      rfl

theorem cell22_1341848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 2, 3, 3].length) (baseStart_1341848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1341848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1341848 prefixEnd_1341848 := by exact prefixLift 1341848
  have htrace : WordTrace (prefixWord ++ tailWord_1341848) baseStart_1341848 baseEnd_1341848 := by
    simpa [prefixWord, tailWord_1341848, baseEnd_1341848] using wordTrace_append hprefix tailTrace_1341848
  have hstable : (prefixWord ++ tailWord_1341848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341848).length < 2 ^ (prefixWord ++ tailWord_1341848).sum := by decide
  have hdescent : baseEnd_1341848 < baseStart_1341848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341908 : List Nat := [2, 4, 1, 2, 2, 1, 1, 4, 1, 4]
def baseStart_1341908 : Nat := 118140960795 + 1341908 * 2 ^ 59
def prefixEnd_1341908 : Nat := 4983230072969 + 3 ^ 40 * 1341908 * 2
def baseEnd_1341908 : Nat := 459362532075760674985789

theorem tailTrace_1341908 : CollatzResearch.WordTrace tailWord_1341908 prefixEnd_1341908 459362532075760674985789 := by
  unfold tailWord_1341908
  simp only [CollatzResearch.WordTrace]
  refine ⟨24471702811251985242793189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32628937081669313657057585 24471702811251985242793189)
  ·
    refine ⟨4588444277109747233023723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24471702811251985242793189 4588444277109747233023723)
    ·
      refine ⟨6882666415664620849535585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4588444277109747233023723 6882666415664620849535585)
      ·
        refine ⟨5161999811748465637151689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6882666415664620849535585 5161999811748465637151689)
        ·
          refine ⟨3871499858811349227863767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5161999811748465637151689 3871499858811349227863767)
          ·
            refine ⟨5807249788217023841795651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3871499858811349227863767 5807249788217023841795651)
            ·
              refine ⟨8710874682325535762693477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5807249788217023841795651 8710874682325535762693477)
              ·
                refine ⟨1633289002936037955505027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8710874682325535762693477 1633289002936037955505027)
                ·
                  refine ⟨2449933504404056933257541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1633289002936037955505027 2449933504404056933257541)
                  ·
                    refine ⟨459362532075760674985789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2449933504404056933257541 459362532075760674985789)
                    ·
                      rfl

theorem cell22_1341908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_1341908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1341908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1341908 prefixEnd_1341908 := by exact prefixLift 1341908
  have htrace : WordTrace (prefixWord ++ tailWord_1341908) baseStart_1341908 baseEnd_1341908 := by
    simpa [prefixWord, tailWord_1341908, baseEnd_1341908] using wordTrace_append hprefix tailTrace_1341908
  have hstable : (prefixWord ++ tailWord_1341908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341908).length < 2 ^ (prefixWord ++ tailWord_1341908).sum := by decide
  have hdescent : baseEnd_1341908 < baseStart_1341908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341921 : List Nat := [1, 2, 3, 1, 2, 2, 1, 1, 6, 3]
def baseStart_1341921 : Nat := 118140960795 + 1341921 * 2 ^ 59
def prefixEnd_1341921 : Nat := 4983230072969 + 3 ^ 40 * 1341921 * 2
def baseEnd_1341921 : Nat := 459366982241432974410749

theorem tailTrace_1341921 : CollatzResearch.WordTrace tailWord_1341921 prefixEnd_1341921 459366982241432974410749 := by
  unfold tailWord_1341921
  simp only [CollatzResearch.WordTrace]
  refine ⟨48943879771456873705809617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32629253180971249137206411 48943879771456873705809617)
  ·
    refine ⟨36707909828592655279357213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48943879771456873705809617 36707909828592655279357213)
    ·
      refine ⟨13765466185722245729758955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36707909828592655279357213 13765466185722245729758955)
      ·
        refine ⟨20648199278583368594638433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13765466185722245729758955 20648199278583368594638433)
        ·
          refine ⟨15486149458937526445978825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20648199278583368594638433 15486149458937526445978825)
          ·
            refine ⟨11614612094203144834484119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15486149458937526445978825 11614612094203144834484119)
            ·
              refine ⟨17421918141304717251726179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11614612094203144834484119 17421918141304717251726179)
              ·
                refine ⟨26132877211957075877589269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17421918141304717251726179 26132877211957075877589269)
                ·
                  refine ⟨1224978619310487931761997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 26132877211957075877589269 1224978619310487931761997)
                  ·
                    refine ⟨459366982241432974410749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1224978619310487931761997 459366982241432974410749)
                    ·
                      rfl

theorem cell22_1341921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 6, 3].length) (baseStart_1341921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1341921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1341921 prefixEnd_1341921 := by exact prefixLift 1341921
  have htrace : WordTrace (prefixWord ++ tailWord_1341921) baseStart_1341921 baseEnd_1341921 := by
    simpa [prefixWord, tailWord_1341921, baseEnd_1341921] using wordTrace_append hprefix tailTrace_1341921
  have hstable : (prefixWord ++ tailWord_1341921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341921).length < 2 ^ (prefixWord ++ tailWord_1341921).sum := by decide
  have hdescent : baseEnd_1341921 < baseStart_1341921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341936 : List Nat := [2, 1, 1, 1, 3, 3, 3, 2, 2, 4]
def baseStart_1341936 : Nat := 118140960795 + 1341936 * 2 ^ 59
def prefixEnd_1341936 : Nat := 4983230072969 + 3 ^ 40 * 1341936 * 2
def baseEnd_1341936 : Nat := 459372117047977935285703

theorem tailTrace_1341936 : CollatzResearch.WordTrace tailWord_1341936 prefixEnd_1341936 459372117047977935285703 := by
  unfold tailWord_1341936
  simp only [CollatzResearch.WordTrace]
  refine ⟨24472213433201265633802831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32629617910935020845070441 24472213433201265633802831)
  ·
    refine ⟨36708320149801898450704247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24472213433201265633802831 36708320149801898450704247)
    ·
      refine ⟨55062480224702847676056371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36708320149801898450704247 55062480224702847676056371)
      ·
        refine ⟨82593720337054271514084557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55062480224702847676056371 82593720337054271514084557)
        ·
          refine ⟨30972645126395351817781709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82593720337054271514084557 30972645126395351817781709)
          ·
            refine ⟨11614741922398256931668141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30972645126395351817781709 11614741922398256931668141)
            ·
              refine ⟨4355528220899346349375553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11614741922398256931668141 4355528220899346349375553)
              ·
                refine ⟨3266646165674509762031665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4355528220899346349375553 3266646165674509762031665)
                ·
                  refine ⟨2449984624255882321523749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3266646165674509762031665 2449984624255882321523749)
                  ·
                    refine ⟨459372117047977935285703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2449984624255882321523749 459372117047977935285703)
                    ·
                      rfl

theorem cell22_1341936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 2, 2, 4].length) (baseStart_1341936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1341936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1341936 prefixEnd_1341936 := by exact prefixLift 1341936
  have htrace : WordTrace (prefixWord ++ tailWord_1341936) baseStart_1341936 baseEnd_1341936 := by
    simpa [prefixWord, tailWord_1341936, baseEnd_1341936] using wordTrace_append hprefix tailTrace_1341936
  have hstable : (prefixWord ++ tailWord_1341936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341936).length < 2 ^ (prefixWord ++ tailWord_1341936).sum := by decide
  have hdescent : baseEnd_1341936 < baseStart_1341936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341991 : List Nat := [1, 1, 7, 2, 2, 1, 2, 2, 4]
def baseStart_1341991 : Nat := 118140960795 + 1341991 * 2 ^ 59
def prefixEnd_1341991 : Nat := 4983230072969 + 3 ^ 40 * 1341991 * 2
def baseEnd_1341991 : Nat := 153130314890658708386845

theorem tailTrace_1341991 : CollatzResearch.WordTrace tailWord_1341991 prefixEnd_1341991 153130314890658708386845 := by
  unfold tailWord_1341991
  simp only [CollatzResearch.WordTrace]
  refine ⟨48946432881203275660857827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32630955254135517107238551 48946432881203275660857827)
  ·
    refine ⟨73419649321804913491286741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48946432881203275660857827 73419649321804913491286741)
    ·
      refine ⟨1720773030979802659952033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 73419649321804913491286741 1720773030979802659952033)
      ·
        refine ⟨1290579773234851994964025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1720773030979802659952033 1290579773234851994964025)
        ·
          refine ⟨967934829926138996223019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1290579773234851994964025 967934829926138996223019)
          ·
            refine ⟨1451902244889208494334529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 967934829926138996223019 1451902244889208494334529)
            ·
              refine ⟨1088926683666906370750897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1451902244889208494334529 1088926683666906370750897)
              ·
                refine ⟨816695012750179778063173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1088926683666906370750897 816695012750179778063173)
                ·
                  refine ⟨153130314890658708386845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 816695012750179778063173 153130314890658708386845)
                  ·
                    rfl

theorem cell22_1341991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 2, 2, 4].length) (baseStart_1341991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1341991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1341991 prefixEnd_1341991 := by exact prefixLift 1341991
  have htrace : WordTrace (prefixWord ++ tailWord_1341991) baseStart_1341991 baseEnd_1341991 := by
    simpa [prefixWord, tailWord_1341991, baseEnd_1341991] using wordTrace_append hprefix tailTrace_1341991
  have hstable : (prefixWord ++ tailWord_1341991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341991).length < 2 ^ (prefixWord ++ tailWord_1341991).sum := by decide
  have hdescent : baseEnd_1341991 < baseStart_1341991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342013 : List Nat := [1, 4, 1, 3, 2, 1, 2, 3, 5]
def baseStart_1342013 : Nat := 118140960795 + 1342013 * 2 ^ 59
def prefixEnd_1342013 : Nat := 4983230072969 + 3 ^ 40 * 1342013 * 2
def baseEnd_1342013 : Nat := 153132825240525133703489

theorem tailTrace_1342013 : CollatzResearch.WordTrace tailWord_1342013 prefixEnd_1342013 153132825240525133703489 := by
  unfold tailWord_1342013
  simp only [CollatzResearch.WordTrace]
  refine ⟨48947235287123573418158693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32631490191415715612105795 48947235287123573418158693)
  ·
    refine ⟨9177606616335670015904755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48947235287123573418158693 9177606616335670015904755)
    ·
      refine ⟨13766409924503505023857133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9177606616335670015904755 13766409924503505023857133)
      ·
        refine ⟨5162403721688814383946425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13766409924503505023857133 5162403721688814383946425)
        ·
          refine ⟨3871802791266610787959819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5162403721688814383946425 3871802791266610787959819)
          ·
            refine ⟨5807704186899916181939729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3871802791266610787959819 5807704186899916181939729)
            ·
              refine ⟨4355778140174937136454797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5807704186899916181939729 4355778140174937136454797)
              ·
                refine ⟨1633416802565601426170549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4355778140174937136454797 1633416802565601426170549)
                ·
                  refine ⟨153132825240525133703489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1633416802565601426170549 153132825240525133703489)
                  ·
                    rfl

theorem cell22_1342013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 3, 5].length) (baseStart_1342013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1342013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1342013 prefixEnd_1342013 := by exact prefixLift 1342013
  have htrace : WordTrace (prefixWord ++ tailWord_1342013) baseStart_1342013 baseEnd_1342013 := by
    simpa [prefixWord, tailWord_1342013, baseEnd_1342013] using wordTrace_append hprefix tailTrace_1342013
  have hstable : (prefixWord ++ tailWord_1342013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342013).length < 2 ^ (prefixWord ++ tailWord_1342013).sum := by decide
  have hdescent : baseEnd_1342013 < baseStart_1342013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342058 : List Nat := [3, 1, 3, 2, 1, 1, 4, 1, 6]
def baseStart_1342058 : Nat := 118140960795 + 1342058 * 2 ^ 59
def prefixEnd_1342058 : Nat := 4983230072969 + 3 ^ 40 * 1342058 * 2
def baseEnd_1342058 : Nat := 153137960047070094578443

theorem tailTrace_1342058 : CollatzResearch.WordTrace tailWord_1342058 prefixEnd_1342058 153137960047070094578443 := by
  unfold tailWord_1342058
  simp only [CollatzResearch.WordTrace]
  refine ⟨12237219142990136525886707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32632584381307030735697885 12237219142990136525886707)
  ·
    refine ⟨18355828714485204788830061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12237219142990136525886707 18355828714485204788830061)
    ·
      refine ⟨6883435767931951795811273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18355828714485204788830061 6883435767931951795811273)
      ·
        refine ⟨5162576825948963846858455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6883435767931951795811273 5162576825948963846858455)
        ·
          refine ⟨7743865238923445770287683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5162576825948963846858455 7743865238923445770287683)
          ·
            refine ⟨11615797858385168655431525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7743865238923445770287683 11615797858385168655431525)
            ·
              refine ⟨2177962098447219122893411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11615797858385168655431525 2177962098447219122893411)
              ·
                refine ⟨3266943147670828684340117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2177962098447219122893411 3266943147670828684340117)
                ·
                  refine ⟨153137960047070094578443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3266943147670828684340117 153137960047070094578443)
                  ·
                    rfl

theorem cell22_1342058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 1, 6].length) (baseStart_1342058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1342058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1342058 prefixEnd_1342058 := by exact prefixLift 1342058
  have htrace : WordTrace (prefixWord ++ tailWord_1342058) baseStart_1342058 baseEnd_1342058 := by
    simpa [prefixWord, tailWord_1342058, baseEnd_1342058] using wordTrace_append hprefix tailTrace_1342058
  have hstable : (prefixWord ++ tailWord_1342058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342058).length < 2 ^ (prefixWord ++ tailWord_1342058).sum := by decide
  have hdescent : baseEnd_1342058 < baseStart_1342058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342071 : List Nat := [1, 1, 3, 1, 1, 3, 3, 2, 1, 6]
def baseStart_1342071 : Nat := 118140960795 + 1342071 * 2 ^ 59
def prefixEnd_1342071 : Nat := 4983230072969 + 3 ^ 40 * 1342071 * 2
def baseEnd_1342071 : Nat := 459418330306882583160289

theorem tailTrace_1342071 : CollatzResearch.WordTrace tailWord_1342071 prefixEnd_1342071 459418330306882583160289 := by
  unfold tailWord_1342071
  simp only [CollatzResearch.WordTrace]
  refine ⟨48949350720913449323770067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32632900480608966215846711 48949350720913449323770067)
  ·
    refine ⟨73424026081370173985655101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48949350720913449323770067 73424026081370173985655101)
    ·
      refine ⟨27534009780513815244620663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73424026081370173985655101 27534009780513815244620663)
      ·
        refine ⟨41301014670770722866930995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27534009780513815244620663 41301014670770722866930995)
        ·
          refine ⟨61951522006156084300396493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41301014670770722866930995 61951522006156084300396493)
          ·
            refine ⟨23231820752308531612648685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61951522006156084300396493 23231820752308531612648685)
            ·
              refine ⟨8711932782115699354743257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23231820752308531612648685 8711932782115699354743257)
              ·
                refine ⟨6533949586586774516057443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8711932782115699354743257 6533949586586774516057443)
                ·
                  refine ⟨9800924379880161774086165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6533949586586774516057443 9800924379880161774086165)
                  ·
                    refine ⟨459418330306882583160289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9800924379880161774086165 459418330306882583160289)
                    ·
                      rfl

theorem cell22_1342071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 6].length) (baseStart_1342071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1342071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1342071 prefixEnd_1342071 := by exact prefixLift 1342071
  have htrace : WordTrace (prefixWord ++ tailWord_1342071) baseStart_1342071 baseEnd_1342071 := by
    simpa [prefixWord, tailWord_1342071, baseEnd_1342071] using wordTrace_append hprefix tailTrace_1342071
  have hstable : (prefixWord ++ tailWord_1342071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342071).length < 2 ^ (prefixWord ++ tailWord_1342071).sum := by decide
  have hdescent : baseEnd_1342071 < baseStart_1342071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342073 : List Nat := [1, 2, 1, 3, 3, 2, 3, 1, 1, 5]
def baseStart_1342073 : Nat := 118140960795 + 1342073 * 2 ^ 59
def prefixEnd_1342073 : Nat := 4983230072969 + 3 ^ 40 * 1342073 * 2
def baseEnd_1342073 : Nat := 459419014947755244610283

theorem tailTrace_1342073 : CollatzResearch.WordTrace tailWord_1342073 prefixEnd_1342073 459419014947755244610283 := by
  unfold tailWord_1342073
  simp only [CollatzResearch.WordTrace]
  refine ⟨48949423666906203665342873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32632949111270802443561915 48949423666906203665342873)
  ·
    refine ⟨36712067750179652749007155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48949423666906203665342873 36712067750179652749007155)
    ·
      refine ⟨55068101625269479123510733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36712067750179652749007155 55068101625269479123510733)
      ·
        refine ⟨20650538109476054671316525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55068101625269479123510733 20650538109476054671316525)
        ·
          refine ⟨7743951791053520501743697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20650538109476054671316525 7743951791053520501743697)
          ·
            refine ⟨5807963843290140376307773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7743951791053520501743697 5807963843290140376307773)
            ·
              refine ⟨2177986441233802641115415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5807963843290140376307773 2177986441233802641115415)
              ·
                refine ⟨3266979661850703961673123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2177986441233802641115415 3266979661850703961673123)
                ·
                  refine ⟨4900469492776055942509685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3266979661850703961673123 4900469492776055942509685)
                  ·
                    refine ⟨459419014947755244610283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4900469492776055942509685 459419014947755244610283)
                    ·
                      rfl

theorem cell22_1342073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 1, 1, 5].length) (baseStart_1342073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1342073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1342073 prefixEnd_1342073 := by exact prefixLift 1342073
  have htrace : WordTrace (prefixWord ++ tailWord_1342073) baseStart_1342073 baseEnd_1342073 := by
    simpa [prefixWord, tailWord_1342073, baseEnd_1342073] using wordTrace_append hprefix tailTrace_1342073
  have hstable : (prefixWord ++ tailWord_1342073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342073).length < 2 ^ (prefixWord ++ tailWord_1342073).sum := by decide
  have hdescent : baseEnd_1342073 < baseStart_1342073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342193 : List Nat := [1, 2, 2, 2, 2, 2, 3, 2, 6]
def baseStart_1342193 : Nat := 118140960795 + 1342193 * 2 ^ 59
def prefixEnd_1342193 : Nat := 4983230072969 + 3 ^ 40 * 1342193 * 2
def baseEnd_1342193 : Nat := 153153364466704977203305

theorem tailTrace_1342193 : CollatzResearch.WordTrace tailWord_1342193 prefixEnd_1342193 153153364466704977203305 := by
  unfold tailWord_1342193
  simp only [CollatzResearch.WordTrace]
  refine ⟨48953800426471464159711233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32635866950980976106474155 48953800426471464159711233)
  ·
    refine ⟨36715350319853598119783425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48953800426471464159711233 36715350319853598119783425)
    ·
      refine ⟨27536512739890198589837569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36715350319853598119783425 27536512739890198589837569)
      ·
        refine ⟨20652384554917648942378177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27536512739890198589837569 20652384554917648942378177)
        ·
          refine ⟨15489288416188236706783633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20652384554917648942378177 15489288416188236706783633)
          ·
            refine ⟨11616966312141177530087725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15489288416188236706783633 11616966312141177530087725)
            ·
              refine ⟨4356362367052941573782897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11616966312141177530087725 4356362367052941573782897)
              ·
                refine ⟨3267271775289706180337173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4356362367052941573782897 3267271775289706180337173)
                ·
                  refine ⟨153153364466704977203305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3267271775289706180337173 153153364466704977203305)
                  ·
                    rfl

theorem cell22_1342193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2, 6].length) (baseStart_1342193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1342193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1342193 prefixEnd_1342193 := by exact prefixLift 1342193
  have htrace : WordTrace (prefixWord ++ tailWord_1342193) baseStart_1342193 baseEnd_1342193 := by
    simpa [prefixWord, tailWord_1342193, baseEnd_1342193] using wordTrace_append hprefix tailTrace_1342193
  have hstable : (prefixWord ++ tailWord_1342193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342193).length < 2 ^ (prefixWord ++ tailWord_1342193).sum := by decide
  have hdescent : baseEnd_1342193 < baseStart_1342193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342223 : List Nat := [1, 1, 2, 1, 1, 1, 6, 1, 4, 4]
def baseStart_1342223 : Nat := 118140960795 + 1342223 * 2 ^ 59
def prefixEnd_1342223 : Nat := 4983230072969 + 3 ^ 40 * 1342223 * 2
def baseEnd_1342223 : Nat := 459470363013204853359823

theorem tailTrace_1342223 : CollatzResearch.WordTrace tailWord_1342223 prefixEnd_1342223 459470363013204853359823 := by
  unfold tailWord_1342223
  simp only [CollatzResearch.WordTrace]
  refine ⟨48954894616362779283303323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32636596410908519522202215 48954894616362779283303323)
  ·
    refine ⟨73432341924544168924954985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48954894616362779283303323 73432341924544168924954985)
    ·
      refine ⟨55074256443408126693716239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73432341924544168924954985 55074256443408126693716239)
      ·
        refine ⟨82611384665112190040574359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55074256443408126693716239 82611384665112190040574359)
        ·
          refine ⟨123917076997668285060861539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82611384665112190040574359 123917076997668285060861539)
          ·
            refine ⟨185875615496502427591292309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123917076997668285060861539 185875615496502427591292309)
            ·
              refine ⟨8712919476398551293341827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 185875615496502427591292309 8712919476398551293341827)
              ·
                refine ⟨13069379214597826940012741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8712919476398551293341827 13069379214597826940012741)
                ·
                  refine ⟨2450508602737092551252389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13069379214597826940012741 2450508602737092551252389)
                  ·
                    refine ⟨459470363013204853359823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2450508602737092551252389 459470363013204853359823)
                    ·
                      rfl

theorem cell22_1342223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 4, 4].length) (baseStart_1342223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1342223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1342223 prefixEnd_1342223 := by exact prefixLift 1342223
  have htrace : WordTrace (prefixWord ++ tailWord_1342223) baseStart_1342223 baseEnd_1342223 := by
    simpa [prefixWord, tailWord_1342223, baseEnd_1342223] using wordTrace_append hprefix tailTrace_1342223
  have hstable : (prefixWord ++ tailWord_1342223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342223).length < 2 ^ (prefixWord ++ tailWord_1342223).sum := by decide
  have hdescent : baseEnd_1342223 < baseStart_1342223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342242 : List Nat := [3, 3, 1, 1, 2, 4, 1, 1, 1, 5]
def baseStart_1342242 : Nat := 118140960795 + 1342242 * 2 ^ 59
def prefixEnd_1342242 : Nat := 4983230072969 + 3 ^ 40 * 1342242 * 2
def baseEnd_1342242 : Nat := 459476867101495137134765

theorem tailTrace_1342242 : CollatzResearch.WordTrace tailWord_1342242 prefixEnd_1342242 459476867101495137134765 := by
  unfold tailWord_1342242
  simp only [CollatzResearch.WordTrace]
  refine ⟨12238896900823486382061245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32637058402195963685496653 12238896900823486382061245)
  ·
    refine ⟨4589586337808807393272967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12238896900823486382061245 4589586337808807393272967)
    ·
      refine ⟨6884379506713211089909451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4589586337808807393272967 6884379506713211089909451)
      ·
        refine ⟨10326569260069816634864177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6884379506713211089909451 10326569260069816634864177)
        ·
          refine ⟨7744926945052362476148133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10326569260069816634864177 7744926945052362476148133)
          ·
            refine ⟨1452173802197317964277775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7744926945052362476148133 1452173802197317964277775)
            ·
              refine ⟨2178260703295976946416663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1452173802197317964277775 2178260703295976946416663)
              ·
                refine ⟨3267391054943965419624995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2178260703295976946416663 3267391054943965419624995)
                ·
                  refine ⟨4901086582415948129437493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3267391054943965419624995 4901086582415948129437493)
                  ·
                    refine ⟨459476867101495137134765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4901086582415948129437493 459476867101495137134765)
                    ·
                      rfl

theorem cell22_1342242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_1342242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1342242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1342242 prefixEnd_1342242 := by exact prefixLift 1342242
  have htrace : WordTrace (prefixWord ++ tailWord_1342242) baseStart_1342242 baseEnd_1342242 := by
    simpa [prefixWord, tailWord_1342242, baseEnd_1342242] using wordTrace_append hprefix tailTrace_1342242
  have hstable : (prefixWord ++ tailWord_1342242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342242).length < 2 ^ (prefixWord ++ tailWord_1342242).sum := by decide
  have hdescent : baseEnd_1342242 < baseStart_1342242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342268 : List Nat := [2, 2, 2, 2, 1, 1, 1, 2, 1, 8]
def baseStart_1342268 : Nat := 118140960795 + 1342268 * 2 ^ 59
def prefixEnd_1342268 : Nat := 4983230072969 + 3 ^ 40 * 1342268 * 2
def baseEnd_1342268 : Nat := 459485767432839735984685

theorem tailTrace_1342268 : CollatzResearch.WordTrace tailWord_1342268 prefixEnd_1342268 459485767432839735984685 := by
  unfold tailWord_1342268
  simp only [CollatzResearch.WordTrace]
  refine ⟨24478267950599875984345729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32637690600799834645794305 24478267950599875984345729)
  ·
    refine ⟨18358700962949906988259297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24478267950599875984345729 18358700962949906988259297)
    ·
      refine ⟨13769025722212430241194473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18358700962949906988259297 13769025722212430241194473)
      ·
        refine ⟨10326769291659322680895855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13769025722212430241194473 10326769291659322680895855)
        ·
          refine ⟨15490153937488984021343783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10326769291659322680895855 15490153937488984021343783)
          ·
            refine ⟨23235230906233476032015675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15490153937488984021343783 23235230906233476032015675)
            ·
              refine ⟨34852846359350214048023513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23235230906233476032015675 34852846359350214048023513)
              ·
                refine ⟨26139634769512660536017635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34852846359350214048023513 26139634769512660536017635)
                ·
                  refine ⟨39209452154268990804026453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26139634769512660536017635 39209452154268990804026453)
                  ·
                    refine ⟨459485767432839735984685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 39209452154268990804026453 459485767432839735984685)
                    ·
                      rfl

theorem cell22_1342268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_1342268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1342268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1342268 prefixEnd_1342268 := by exact prefixLift 1342268
  have htrace : WordTrace (prefixWord ++ tailWord_1342268) baseStart_1342268 baseEnd_1342268 := by
    simpa [prefixWord, tailWord_1342268, baseEnd_1342268] using wordTrace_append hprefix tailTrace_1342268
  have hstable : (prefixWord ++ tailWord_1342268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342268).length < 2 ^ (prefixWord ++ tailWord_1342268).sum := by decide
  have hdescent : baseEnd_1342268 < baseStart_1342268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342278 : List Nat := [6, 1, 1, 2, 2, 1, 3, 2, 4]
def baseStart_1342278 : Nat := 118140960795 + 1342278 * 2 ^ 59
def prefixEnd_1342278 : Nat := 4983230072969 + 3 ^ 40 * 1342278 * 2
def baseEnd_1342278 : Nat := 153163063545734347744885

theorem tailTrace_1342278 : CollatzResearch.WordTrace tailWord_1342278 prefixEnd_1342278 153163063545734347744885 := by
  unfold tailWord_1342278
  simp only [CollatzResearch.WordTrace]
  refine ⟨1529903144723860114892359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 32637933754109015784370325 1529903144723860114892359)
  ·
    refine ⟨2294854717085790172338539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1529903144723860114892359 2294854717085790172338539)
    ·
      refine ⟨3442282075628685258507809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2294854717085790172338539 3442282075628685258507809)
      ·
        refine ⟨2581711556721513943880857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3442282075628685258507809 2581711556721513943880857)
        ·
          refine ⟨1936283667541135457910643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2581711556721513943880857 1936283667541135457910643)
          ·
            refine ⟨2904425501311703186865965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1936283667541135457910643 2904425501311703186865965)
            ·
              refine ⟨1089159562991888695074737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2904425501311703186865965 1089159562991888695074737)
              ·
                refine ⟨816869672243916521306053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1089159562991888695074737 816869672243916521306053)
                ·
                  refine ⟨153163063545734347744885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 816869672243916521306053 153163063545734347744885)
                  ·
                    rfl

theorem cell22_1342278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_1342278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1342278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1342278 prefixEnd_1342278 := by exact prefixLift 1342278
  have htrace : WordTrace (prefixWord ++ tailWord_1342278) baseStart_1342278 baseEnd_1342278 := by
    simpa [prefixWord, tailWord_1342278, baseEnd_1342278] using wordTrace_append hprefix tailTrace_1342278
  have hstable : (prefixWord ++ tailWord_1342278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342278).length < 2 ^ (prefixWord ++ tailWord_1342278).sum := by decide
  have hdescent : baseEnd_1342278 < baseStart_1342278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342328 : List Nat := [2, 1, 2, 1, 1, 1, 1, 3, 10]
def baseStart_1342328 : Nat := 118140960795 + 1342328 * 2 ^ 59
def prefixEnd_1342328 : Nat := 4983230072969 + 3 ^ 40 * 1342328 * 2
def baseEnd_1342328 : Nat := 153168768886339859828167

theorem tailTrace_1342328 : CollatzResearch.WordTrace tailWord_1342328 prefixEnd_1342328 153168768886339859828167 := by
  unfold tailWord_1342328
  simp only [CollatzResearch.WordTrace]
  refine ⟨24479362140491191107937819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32639149520654921477250425 24479362140491191107937819)
  ·
    refine ⟨36719043210736786661906729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24479362140491191107937819 36719043210736786661906729)
    ·
      refine ⟨27539282408052589996430047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36719043210736786661906729 27539282408052589996430047)
      ·
        refine ⟨41308923612078884994645071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27539282408052589996430047 41308923612078884994645071)
        ·
          refine ⟨61963385418118327491967607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41308923612078884994645071 61963385418118327491967607)
          ·
            refine ⟨92945078127177491237951411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61963385418118327491967607 92945078127177491237951411)
            ·
              refine ⟨139417617190766236856927117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92945078127177491237951411 139417617190766236856927117)
              ·
                refine ⟨52281606446537338821347669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 139417617190766236856927117 52281606446537338821347669)
                ·
                  refine ⟨153168768886339859828167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 52281606446537338821347669 153168768886339859828167)
                  ·
                    rfl

theorem cell22_1342328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 10].length) (baseStart_1342328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1342328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1342328 prefixEnd_1342328 := by exact prefixLift 1342328
  have htrace : WordTrace (prefixWord ++ tailWord_1342328) baseStart_1342328 baseEnd_1342328 := by
    simpa [prefixWord, tailWord_1342328, baseEnd_1342328] using wordTrace_append hprefix tailTrace_1342328
  have hstable : (prefixWord ++ tailWord_1342328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342328).length < 2 ^ (prefixWord ++ tailWord_1342328).sum := by decide
  have hdescent : baseEnd_1342328 < baseStart_1342328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342362 : List Nat := [3, 1, 1, 4, 3, 1, 1, 2, 6]
def baseStart_1342362 : Nat := 118140960795 + 1342362 * 2 ^ 59
def prefixEnd_1342362 : Nat := 4983230072969 + 3 ^ 40 * 1342362 * 2
def baseEnd_1342362 : Nat := 153172648517951608044799

theorem tailTrace_1342362 : CollatzResearch.WordTrace tailWord_1342362 prefixEnd_1342362 153172648517951608044799 := by
  unfold tailWord_1342362
  simp only [CollatzResearch.WordTrace]
  refine ⟨12239991090714801505653335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32639976241906137348408893 12239991090714801505653335)
  ·
    refine ⟨18359986636072202258480003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12239991090714801505653335 18359986636072202258480003)
    ·
      refine ⟨27539979954108303387720005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18359986636072202258480003 27539979954108303387720005)
      ·
        refine ⟨5163746241395306885197501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27539979954108303387720005 5163746241395306885197501)
        ·
          refine ⟨1936404840523240081949063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5163746241395306885197501 1936404840523240081949063)
          ·
            refine ⟨2904607260784860122923595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1936404840523240081949063 2904607260784860122923595)
            ·
              refine ⟨4356910891177290184385393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2904607260784860122923595 4356910891177290184385393)
              ·
                refine ⟨3267683168382967638289045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4356910891177290184385393 3267683168382967638289045)
                ·
                  refine ⟨153172648517951608044799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3267683168382967638289045 153172648517951608044799)
                  ·
                    rfl

theorem cell22_1342362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 2, 6].length) (baseStart_1342362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1342362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1342362 prefixEnd_1342362 := by exact prefixLift 1342362
  have htrace : WordTrace (prefixWord ++ tailWord_1342362) baseStart_1342362 baseEnd_1342362 := by
    simpa [prefixWord, tailWord_1342362, baseEnd_1342362] using wordTrace_append hprefix tailTrace_1342362
  have hstable : (prefixWord ++ tailWord_1342362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342362).length < 2 ^ (prefixWord ++ tailWord_1342362).sum := by decide
  have hdescent : baseEnd_1342362 < baseStart_1342362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342381 : List Nat := [1, 5, 2, 3, 1, 1, 1, 3, 1, 4]
def baseStart_1342381 : Nat := 118140960795 + 1342381 * 2 ^ 59
def prefixEnd_1342381 : Nat := 4983230072969 + 3 ^ 40 * 1342381 * 2
def baseEnd_1342381 : Nat := 459524449642145107909339

theorem tailTrace_1342381 : CollatzResearch.WordTrace tailWord_1342381 prefixEnd_1342381 459524449642145107909339 := by
  unfold tailWord_1342381
  simp only [CollatzResearch.WordTrace]
  refine ⟨48960657349790372267554997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32640438233193581511703331 48960657349790372267554997)
  ·
    refine ⟨4590061626542847400083281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48960657349790372267554997 4590061626542847400083281)
    ·
      refine ⟨3442546219907135550062461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4590061626542847400083281 3442546219907135550062461)
      ·
        refine ⟨1290954832465175831273423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3442546219907135550062461 1290954832465175831273423)
        ·
          refine ⟨1936432248697763746910135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1290954832465175831273423 1936432248697763746910135)
          ·
            refine ⟨2904648373046645620365203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1936432248697763746910135 2904648373046645620365203)
            ·
              refine ⟨4356972559569968430547805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2904648373046645620365203 4356972559569968430547805)
              ·
                refine ⟨1633864709838738161455427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4356972559569968430547805 1633864709838738161455427)
                ·
                  refine ⟨2450797064758107242183141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1633864709838738161455427 2450797064758107242183141)
                  ·
                    refine ⟨459524449642145107909339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2450797064758107242183141 459524449642145107909339)
                    ·
                      rfl

theorem cell22_1342381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_1342381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1342381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1342381 prefixEnd_1342381 := by exact prefixLift 1342381
  have htrace : WordTrace (prefixWord ++ tailWord_1342381) baseStart_1342381 baseEnd_1342381 := by
    simpa [prefixWord, tailWord_1342381, baseEnd_1342381] using wordTrace_append hprefix tailTrace_1342381
  have hstable : (prefixWord ++ tailWord_1342381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342381).length < 2 ^ (prefixWord ++ tailWord_1342381).sum := by decide
  have hdescent : baseEnd_1342381 < baseStart_1342381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342435 : List Nat := [1, 1, 1, 6, 1, 1, 1, 1, 9]
def baseStart_1342435 : Nat := 118140960795 + 1342435 * 2 ^ 59
def prefixEnd_1342435 : Nat := 4983230072969 + 3 ^ 40 * 1342435 * 2
def baseEnd_1342435 : Nat := 153180978315235655686391

theorem tailTrace_1342435 : CollatzResearch.WordTrace tailWord_1342435 prefixEnd_1342435 153180978315235655686391 := by
  unfold tailWord_1342435
  simp only [CollatzResearch.WordTrace]
  refine ⟨48962626891594739490020759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32641751261063159660013839 48962626891594739490020759)
  ·
    refine ⟨73443940337392109235031139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48962626891594739490020759 73443940337392109235031139)
    ·
      refine ⟨110165910506088163852546709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73443940337392109235031139 110165910506088163852546709)
      ·
        refine ⟨5164027054972882680588127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 110165910506088163852546709 5164027054972882680588127)
        ·
          refine ⟨7746040582459324020882191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5164027054972882680588127 7746040582459324020882191)
          ·
            refine ⟨11619060873688986031323287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7746040582459324020882191 11619060873688986031323287)
            ·
              refine ⟨17428591310533479046984931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11619060873688986031323287 17428591310533479046984931)
              ·
                refine ⟨26142886965800218570477397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17428591310533479046984931 26142886965800218570477397)
                ·
                  refine ⟨153180978315235655686391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 26142886965800218570477397 153180978315235655686391)
                  ·
                    rfl

theorem cell22_1342435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 9].length) (baseStart_1342435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1342435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1342435 prefixEnd_1342435 := by exact prefixLift 1342435
  have htrace : WordTrace (prefixWord ++ tailWord_1342435) baseStart_1342435 baseEnd_1342435 := by
    simpa [prefixWord, tailWord_1342435, baseEnd_1342435] using wordTrace_append hprefix tailTrace_1342435
  have hstable : (prefixWord ++ tailWord_1342435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342435).length < 2 ^ (prefixWord ++ tailWord_1342435).sum := by decide
  have hdescent : baseEnd_1342435 < baseStart_1342435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342514 : List Nat := [3, 2, 1, 1, 2, 2, 3, 4, 4]
def baseStart_1342514 : Nat := 118140960795 + 1342514 * 2 ^ 59
def prefixEnd_1342514 : Nat := 4983230072969 + 3 ^ 40 * 1342514 * 2
def baseEnd_1342514 : Nat := 153189992753392364777977

theorem tailTrace_1342514 : CollatzResearch.WordTrace tailWord_1342514 prefixEnd_1342514 153189992753392364777977 := by
  unfold tailWord_1342514
  simp only [CollatzResearch.WordTrace]
  refine ⟨12241377064577133995536649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32643672172205690654764397 12241377064577133995536649)
  ·
    refine ⟨9181032798432850496652487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12241377064577133995536649 9181032798432850496652487)
    ·
      refine ⟨13771549197649275744978731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9181032798432850496652487 13771549197649275744978731)
      ·
        refine ⟨20657323796473913617468097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13771549197649275744978731 20657323796473913617468097)
        ·
          refine ⟨15492992847355435213101073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20657323796473913617468097 15492992847355435213101073)
          ·
            refine ⟨11619744635516576409825805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15492992847355435213101073 11619744635516576409825805)
            ·
              refine ⟨4357404238318716153684677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11619744635516576409825805 4357404238318716153684677)
              ·
                refine ⟨817013294684759278815877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4357404238318716153684677 817013294684759278815877)
                ·
                  refine ⟨153189992753392364777977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 817013294684759278815877 153189992753392364777977)
                  ·
                    rfl

theorem cell22_1342514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 4, 4].length) (baseStart_1342514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1342514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1342514 prefixEnd_1342514 := by exact prefixLift 1342514
  have htrace : WordTrace (prefixWord ++ tailWord_1342514) baseStart_1342514 baseEnd_1342514 := by
    simpa [prefixWord, tailWord_1342514, baseEnd_1342514] using wordTrace_append hprefix tailTrace_1342514
  have hstable : (prefixWord ++ tailWord_1342514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342514).length < 2 ^ (prefixWord ++ tailWord_1342514).sum := by decide
  have hdescent : baseEnd_1342514 < baseStart_1342514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342587 : List Nat := [1, 1, 1, 1, 1, 4, 1, 7, 5]
def baseStart_1342587 : Nat := 118140960795 + 1342587 * 2 ^ 59
def prefixEnd_1342587 : Nat := 4983230072969 + 3 ^ 40 * 1342587 * 2
def baseEnd_1342587 : Nat := 153198322550676412419569

theorem tailTrace_1342587 : CollatzResearch.WordTrace tailWord_1342587 prefixEnd_1342587 153198322550676412419569 := by
  unfold tailWord_1342587
  simp only [CollatzResearch.WordTrace]
  refine ⟨48968170787044069449554015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32645447191362712966369343 48968170787044069449554015)
  ·
    refine ⟨73452256180566104174331023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48968170787044069449554015 73452256180566104174331023)
    ·
      refine ⟨110178384270849156261496535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73452256180566104174331023 110178384270849156261496535)
      ·
        refine ⟨165267576406273734392244803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110178384270849156261496535 165267576406273734392244803)
        ·
          refine ⟨247901364609410601588367205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165267576406273734392244803 247901364609410601588367205)
          ·
            refine ⟨46481505864264487797818851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 247901364609410601588367205 46481505864264487797818851)
            ·
              refine ⟨69722258796396731696728277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46481505864264487797818851 69722258796396731696728277)
              ·
                refine ⟨1634115440540548399142069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 69722258796396731696728277 1634115440540548399142069)
                ·
                  refine ⟨153198322550676412419569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1634115440540548399142069 153198322550676412419569)
                  ·
                    rfl

theorem cell22_1342587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 7, 5].length) (baseStart_1342587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1342587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1342587 prefixEnd_1342587 := by exact prefixLift 1342587
  have htrace : WordTrace (prefixWord ++ tailWord_1342587) baseStart_1342587 baseEnd_1342587 := by
    simpa [prefixWord, tailWord_1342587, baseEnd_1342587] using wordTrace_append hprefix tailTrace_1342587
  have hstable : (prefixWord ++ tailWord_1342587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342587).length < 2 ^ (prefixWord ++ tailWord_1342587).sum := by decide
  have hdescent : baseEnd_1342587 < baseStart_1342587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342617 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 7, 4]
def baseStart_1342617 : Nat := 118140960795 + 1342617 * 2 ^ 59
def prefixEnd_1342617 : Nat := 4983230072969 + 3 ^ 40 * 1342617 * 2
def baseEnd_1342617 : Nat := 459605237265119159008615

theorem tailTrace_1342617 : CollatzResearch.WordTrace tailWord_1342617 prefixEnd_1342617 459605237265119159008615 := by
  unfold tailWord_1342617
  simp only [CollatzResearch.WordTrace]
  refine ⟨48969264976935384573146105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32646176651290256382097403 48969264976935384573146105)
  ·
    refine ⟨36726948732701538429859579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48969264976935384573146105 36726948732701538429859579)
    ·
      refine ⟨55090423099052307644789369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36726948732701538429859579 55090423099052307644789369)
      ·
        refine ⟨41317817324289230733592027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55090423099052307644789369 41317817324289230733592027)
        ·
          refine ⟨61976725986433846100388041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41317817324289230733592027 61976725986433846100388041)
          ·
            refine ⟨46482544489825384575291031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61976725986433846100388041 46482544489825384575291031)
            ·
              refine ⟨69723816734738076862936547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46482544489825384575291031 69723816734738076862936547)
              ·
                refine ⟨104585725102107115294404821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69723816734738076862936547 104585725102107115294404821)
                ·
                  refine ⟨2451227932080635514712613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 104585725102107115294404821 2451227932080635514712613)
                  ·
                    refine ⟨459605237265119159008615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2451227932080635514712613 459605237265119159008615)
                    ·
                      rfl

theorem cell22_1342617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 7, 4].length) (baseStart_1342617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1342617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1342617 prefixEnd_1342617 := by exact prefixLift 1342617
  have htrace : WordTrace (prefixWord ++ tailWord_1342617) baseStart_1342617 baseEnd_1342617 := by
    simpa [prefixWord, tailWord_1342617, baseEnd_1342617] using wordTrace_append hprefix tailTrace_1342617
  have hstable : (prefixWord ++ tailWord_1342617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342617).length < 2 ^ (prefixWord ++ tailWord_1342617).sum := by decide
  have hdescent : baseEnd_1342617 < baseStart_1342617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342664 : List Nat := [2, 1, 3, 1, 2, 1, 2, 1, 6, 3]
def baseStart_1342664 : Nat := 118140960795 + 1342664 * 2 ^ 59
def prefixEnd_1342664 : Nat := 4983230072969 + 3 ^ 40 * 1342664 * 2
def baseEnd_1342664 : Nat := 459621326325626703083471

theorem tailTrace_1342664 : CollatzResearch.WordTrace tailWord_1342664 prefixEnd_1342664 459621326325626703083471 := by
  unfold tailWord_1342664
  simp only [CollatzResearch.WordTrace]
  refine ⟨24485489603882555800053523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32647319471843407733404697 24485489603882555800053523)
  ·
    refine ⟨36728234405823833700080285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24485489603882555800053523 36728234405823833700080285)
    ·
      refine ⟨13773087902183937637530107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36728234405823833700080285 13773087902183937637530107)
      ·
        refine ⟨20659631853275906456295161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13773087902183937637530107 20659631853275906456295161)
        ·
          refine ⟨15494723889956929842221371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20659631853275906456295161 15494723889956929842221371)
          ·
            refine ⟨23242085834935394763332057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15494723889956929842221371 23242085834935394763332057)
            ·
              refine ⟨17431564376201546072499043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23242085834935394763332057 17431564376201546072499043)
              ·
                refine ⟨26147346564302319108748565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17431564376201546072499043 26147346564302319108748565)
                ·
                  refine ⟨1225656870201671208222589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 26147346564302319108748565 1225656870201671208222589)
                  ·
                    refine ⟨459621326325626703083471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1225656870201671208222589 459621326325626703083471)
                    ·
                      rfl

theorem cell22_1342664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 6, 3].length) (baseStart_1342664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1342664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1342664 prefixEnd_1342664 := by exact prefixLift 1342664
  have htrace : WordTrace (prefixWord ++ tailWord_1342664) baseStart_1342664 baseEnd_1342664 := by
    simpa [prefixWord, tailWord_1342664, baseEnd_1342664] using wordTrace_append hprefix tailTrace_1342664
  have hstable : (prefixWord ++ tailWord_1342664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342664).length < 2 ^ (prefixWord ++ tailWord_1342664).sum := by decide
  have hdescent : baseEnd_1342664 < baseStart_1342664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342679 : List Nat := [1, 1, 3, 2, 1, 2, 4, 2, 2, 4]
def baseStart_1342679 : Nat := 118140960795 + 1342679 * 2 ^ 59
def prefixEnd_1342679 : Nat := 4983230072969 + 3 ^ 40 * 1342679 * 2
def baseEnd_1342679 : Nat := 459626461132171663958425

theorem tailTrace_1342679 : CollatzResearch.WordTrace tailWord_1342679 prefixEnd_1342679 459626461132171663958425 := by
  unfold tailWord_1342679
  simp only [CollatzResearch.WordTrace]
  refine ⟨48971526302710769161903091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32647684201807179441268727 48971526302710769161903091)
  ·
    refine ⟨73457289454066153742854637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48971526302710769161903091 73457289454066153742854637)
    ·
      refine ⟨27546483545274807653570489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73457289454066153742854637 27546483545274807653570489)
      ·
        refine ⟨20659862658956105740177867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27546483545274807653570489 20659862658956105740177867)
        ·
          refine ⟨30989793988434158610266801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20659862658956105740177867 30989793988434158610266801)
          ·
            refine ⟨23242345491325618957700101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30989793988434158610266801 23242345491325618957700101)
            ·
              refine ⟨4357939779623553554568769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23242345491325618957700101 4357939779623553554568769)
              ·
                refine ⟨3268454834717665165926577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4357939779623553554568769 3268454834717665165926577)
                ·
                  refine ⟨2451341126038248874444933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3268454834717665165926577 2451341126038248874444933)
                  ·
                    refine ⟨459626461132171663958425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2451341126038248874444933 459626461132171663958425)
                    ·
                      rfl

theorem cell22_1342679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 2, 2, 4].length) (baseStart_1342679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1342679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1342679 prefixEnd_1342679 := by exact prefixLift 1342679
  have htrace : WordTrace (prefixWord ++ tailWord_1342679) baseStart_1342679 baseEnd_1342679 := by
    simpa [prefixWord, tailWord_1342679, baseEnd_1342679] using wordTrace_append hprefix tailTrace_1342679
  have hstable : (prefixWord ++ tailWord_1342679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342679).length < 2 ^ (prefixWord ++ tailWord_1342679).sum := by decide
  have hdescent : baseEnd_1342679 < baseStart_1342679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342743 : List Nat := [1, 1, 3, 4, 1, 1, 1, 6, 1, 3]
def baseStart_1342743 : Nat := 118140960795 + 1342743 * 2 ^ 59
def prefixEnd_1342743 : Nat := 4983230072969 + 3 ^ 40 * 1342743 * 2
def baseEnd_1342743 : Nat := 459648369640096830358229

theorem tailTrace_1342743 : CollatzResearch.WordTrace tailWord_1342743 prefixEnd_1342743 459648369640096830358229 := by
  unfold tailWord_1342743
  simp only [CollatzResearch.WordTrace]
  refine ⟨48973860574478908092232883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32649240382985938728155255 48973860574478908092232883)
  ·
    refine ⟨73460790861718362138349325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48973860574478908092232883 73460790861718362138349325)
    ·
      refine ⟨27547796573144385801880997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73460790861718362138349325 27547796573144385801880997)
      ·
        refine ⟨5165211857464572337852687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27547796573144385801880997 5165211857464572337852687)
        ·
          refine ⟨7747817786196858506779031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5165211857464572337852687 7747817786196858506779031)
          ·
            refine ⟨11621726679295287760168547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7747817786196858506779031 11621726679295287760168547)
            ·
              refine ⟨17432590018942931640252821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11621726679295287760168547 17432590018942931640252821)
              ·
                refine ⟨817152657137949920636851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17432590018942931640252821 817152657137949920636851)
                ·
                  refine ⟨1225728985706924880955277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 817152657137949920636851 1225728985706924880955277)
                  ·
                    refine ⟨459648369640096830358229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1225728985706924880955277 459648369640096830358229)
                    ·
                      rfl

theorem cell22_1342743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 6, 1, 3].length) (baseStart_1342743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1342743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1342743 prefixEnd_1342743 := by exact prefixLift 1342743
  have htrace : WordTrace (prefixWord ++ tailWord_1342743) baseStart_1342743 baseEnd_1342743 := by
    simpa [prefixWord, tailWord_1342743, baseEnd_1342743] using wordTrace_append hprefix tailTrace_1342743
  have hstable : (prefixWord ++ tailWord_1342743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342743).length < 2 ^ (prefixWord ++ tailWord_1342743).sum := by decide
  have hdescent : baseEnd_1342743 < baseStart_1342743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342777 : List Nat := [1, 2, 1, 6, 2, 2, 1, 3, 1, 3]
def baseStart_1342777 : Nat := 118140960795 + 1342777 * 2 ^ 59
def prefixEnd_1342777 : Nat := 4983230072969 + 3 ^ 40 * 1342777 * 2
def baseEnd_1342777 : Nat := 459660008534932075008125

theorem tailTrace_1342777 : CollatzResearch.WordTrace tailWord_1342777 prefixEnd_1342777 459660008534932075008125 := by
  unfold tailWord_1342777
  simp only [CollatzResearch.WordTrace]
  refine ⟨48975100656355731898970585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32650067104237154599313723 48975100656355731898970585)
  ·
    refine ⟨36731325492266798924227939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48975100656355731898970585 36731325492266798924227939)
    ·
      refine ⟨55096988238400198386341909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36731325492266798924227939 55096988238400198386341909)
      ·
        refine ⟨2582671323675009299359777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 55096988238400198386341909 2582671323675009299359777)
        ·
          refine ⟨1937003492756256974519833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2582671323675009299359777 1937003492756256974519833)
          ·
            refine ⟨1452752619567192730889875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1937003492756256974519833 1452752619567192730889875)
            ·
              refine ⟨2179128929350789096334813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1452752619567192730889875 2179128929350789096334813)
              ·
                refine ⟨817173348506545911125555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2179128929350789096334813 817173348506545911125555)
                ·
                  refine ⟨1225760022759818866688333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 817173348506545911125555 1225760022759818866688333)
                  ·
                    refine ⟨459660008534932075008125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1225760022759818866688333 459660008534932075008125)
                    ·
                      rfl

theorem cell22_1342777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 3, 1, 3].length) (baseStart_1342777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1342777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1342777 prefixEnd_1342777 := by exact prefixLift 1342777
  have htrace : WordTrace (prefixWord ++ tailWord_1342777) baseStart_1342777 baseEnd_1342777 := by
    simpa [prefixWord, tailWord_1342777, baseEnd_1342777] using wordTrace_append hprefix tailTrace_1342777
  have hstable : (prefixWord ++ tailWord_1342777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342777).length < 2 ^ (prefixWord ++ tailWord_1342777).sum := by decide
  have hdescent : baseEnd_1342777 < baseStart_1342777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342831 : List Nat := [1, 1, 2, 1, 3, 1, 6, 1, 2, 4]
def baseStart_1342831 : Nat := 118140960795 + 1342831 * 2 ^ 59
def prefixEnd_1342831 : Nat := 4983230072969 + 3 ^ 40 * 1342831 * 2
def baseEnd_1342831 : Nat := 459678493838493934157959

theorem tailTrace_1342831 : CollatzResearch.WordTrace tailWord_1342831 prefixEnd_1342831 459678493838493934157959 := by
  unfold tailWord_1342831
  simp only [CollatzResearch.WordTrace]
  refine ⟨48977070198160099121436347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32651380132106732747624231 48977070198160099121436347)
  ·
    refine ⟨73465605297240148682154521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48977070198160099121436347 73465605297240148682154521)
    ·
      refine ⟨55099203972930111511615891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73465605297240148682154521 55099203972930111511615891)
      ·
        refine ⟨82648805959395167267423837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55099203972930111511615891 82648805959395167267423837)
        ·
          refine ⟨30993302234773187725283939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82648805959395167267423837 30993302234773187725283939)
          ·
            refine ⟨46489953352159781587925909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30993302234773187725283939 46489953352159781587925909)
            ·
              refine ⟨2179216563382489761934027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 46489953352159781587925909 2179216563382489761934027)
              ·
                refine ⟨3268824845073734642901041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2179216563382489761934027 3268824845073734642901041)
                ·
                  refine ⟨2451618633805300982175781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3268824845073734642901041 2451618633805300982175781)
                  ·
                    refine ⟨459678493838493934157959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2451618633805300982175781 459678493838493934157959)
                    ·
                      rfl

theorem cell22_1342831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 1, 2, 4].length) (baseStart_1342831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1342831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1342831 prefixEnd_1342831 := by exact prefixLift 1342831
  have htrace : WordTrace (prefixWord ++ tailWord_1342831) baseStart_1342831 baseEnd_1342831 := by
    simpa [prefixWord, tailWord_1342831, baseEnd_1342831] using wordTrace_append hprefix tailTrace_1342831
  have hstable : (prefixWord ++ tailWord_1342831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342831).length < 2 ^ (prefixWord ++ tailWord_1342831).sum := by decide
  have hdescent : baseEnd_1342831 < baseStart_1342831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342859 : List Nat := [1, 1, 1, 1, 4, 3, 1, 1, 1, 8]
def baseStart_1342859 : Nat := 118140960795 + 1342859 * 2 ^ 59
def prefixEnd_1342859 : Nat := 4983230072969 + 3 ^ 40 * 1342859 * 2
def baseEnd_1342859 : Nat := 459688078810711194457873

theorem tailTrace_1342859 : CollatzResearch.WordTrace tailWord_1342859 prefixEnd_1342859 459688078810711194457873 := by
  unfold tailWord_1342859
  simp only [CollatzResearch.WordTrace]
  refine ⟨48978091442058659903455631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32652060961372439935637087 48978091442058659903455631)
  ·
    refine ⟨73467137163087989855183447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48978091442058659903455631 73467137163087989855183447)
    ·
      refine ⟨110200705744631984782775171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73467137163087989855183447 110200705744631984782775171)
      ·
        refine ⟨165301058616947977174162757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110200705744631984782775171 165301058616947977174162757)
        ·
          refine ⟨30993948490677745720155517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 165301058616947977174162757 30993948490677745720155517)
          ·
            refine ⟨11622730684004154645058319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30993948490677745720155517 11622730684004154645058319)
            ·
              refine ⟨17434096026006231967587479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11622730684004154645058319 17434096026006231967587479)
              ·
                refine ⟨26151144039009347951381219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17434096026006231967587479 26151144039009347951381219)
                ·
                  refine ⟨39226716058514021927071829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26151144039009347951381219 39226716058514021927071829)
                  ·
                    refine ⟨459688078810711194457873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 39226716058514021927071829 459688078810711194457873)
                    ·
                      rfl

theorem cell22_1342859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 8].length) (baseStart_1342859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1342859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1342859 prefixEnd_1342859 := by exact prefixLift 1342859
  have htrace : WordTrace (prefixWord ++ tailWord_1342859) baseStart_1342859 baseEnd_1342859 := by
    simpa [prefixWord, tailWord_1342859, baseEnd_1342859] using wordTrace_append hprefix tailTrace_1342859
  have hstable : (prefixWord ++ tailWord_1342859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342859).length < 2 ^ (prefixWord ++ tailWord_1342859).sum := by decide
  have hdescent : baseEnd_1342859 < baseStart_1342859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342908 : List Nat := [2, 2, 2, 4, 2, 1, 1, 1, 7]
def baseStart_1342908 : Nat := 118140960795 + 1342908 * 2 ^ 59
def prefixEnd_1342908 : Nat := 4983230072969 + 3 ^ 40 * 1342908 * 2
def baseEnd_1342908 : Nat := 153234950837363799994241

theorem tailTrace_1342908 : CollatzResearch.WordTrace tailWord_1342908 prefixEnd_1342908 153234950837363799994241 := by
  unfold tailWord_1342908
  simp only [CollatzResearch.WordTrace]
  refine ⟨24489939309440570635994689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32653252412587427514659585 24489939309440570635994689)
  ·
    refine ⟨18367454482080427976996017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24489939309440570635994689 18367454482080427976996017)
    ·
      refine ⟨13775590861560320982747013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18367454482080427976996017 13775590861560320982747013)
      ·
        refine ⟨2582923286542560184265065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13775590861560320982747013 2582923286542560184265065)
        ·
          refine ⟨1937192464906920138198799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2582923286542560184265065 1937192464906920138198799)
          ·
            refine ⟨2905788697360380207298199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1937192464906920138198799 2905788697360380207298199)
            ·
              refine ⟨4358683046040570310947299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2905788697360380207298199 4358683046040570310947299)
              ·
                refine ⟨6538024569060855466420949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4358683046040570310947299 6538024569060855466420949)
                ·
                  refine ⟨153234950837363799994241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6538024569060855466420949 153234950837363799994241)
                  ·
                    rfl

theorem cell22_1342908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 7].length) (baseStart_1342908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1342908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1342908 prefixEnd_1342908 := by exact prefixLift 1342908
  have htrace : WordTrace (prefixWord ++ tailWord_1342908) baseStart_1342908 baseEnd_1342908 := by
    simpa [prefixWord, tailWord_1342908, baseEnd_1342908] using wordTrace_append hprefix tailTrace_1342908
  have hstable : (prefixWord ++ tailWord_1342908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342908).length < 2 ^ (prefixWord ++ tailWord_1342908).sum := by decide
  have hdescent : baseEnd_1342908 < baseStart_1342908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342936 : List Nat := [2, 1, 2, 2, 2, 1, 4, 2, 6]
def baseStart_1342936 : Nat := 118140960795 + 1342936 * 2 ^ 59
def prefixEnd_1342936 : Nat := 4983230072969 + 3 ^ 40 * 1342936 * 2
def baseEnd_1342936 : Nat := 153238145828102886760879

theorem tailTrace_1342936 : CollatzResearch.WordTrace tailWord_1342936 prefixEnd_1342936 153238145828102886760879 := by
  unfold tailWord_1342936
  simp only [CollatzResearch.WordTrace]
  refine ⟨24490449931389851027004331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32653933241853134702672441 24490449931389851027004331)
  ·
    refine ⟨36735674897084776540506497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24490449931389851027004331 36735674897084776540506497)
    ·
      refine ⟨27551756172813582405379873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36735674897084776540506497 27551756172813582405379873)
      ·
        refine ⟨20663817129610186804034905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27551756172813582405379873 20663817129610186804034905)
        ·
          refine ⟨15497862847207640103026179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20663817129610186804034905 15497862847207640103026179)
          ·
            refine ⟨23246794270811460154539269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15497862847207640103026179 23246794270811460154539269)
            ·
              refine ⟨4358773925777148778976113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23246794270811460154539269 4358773925777148778976113)
              ·
                refine ⟨3269080444332861584232085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4358773925777148778976113 3269080444332861584232085)
                ·
                  refine ⟨153238145828102886760879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3269080444332861584232085 153238145828102886760879)
                  ·
                    rfl

theorem cell22_1342936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 2, 6].length) (baseStart_1342936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1342936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1342936 prefixEnd_1342936 := by exact prefixLift 1342936
  have htrace : WordTrace (prefixWord ++ tailWord_1342936) baseStart_1342936 baseEnd_1342936 := by
    simpa [prefixWord, tailWord_1342936, baseEnd_1342936] using wordTrace_append hprefix tailTrace_1342936
  have hstable : (prefixWord ++ tailWord_1342936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342936).length < 2 ^ (prefixWord ++ tailWord_1342936).sum := by decide
  have hdescent : baseEnd_1342936 < baseStart_1342936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342938 : List Nat := [3, 1, 1, 2, 3, 2, 1, 4, 1, 4]
def baseStart_1342938 : Nat := 118140960795 + 1342938 * 2 ^ 59
def prefixEnd_1342938 : Nat := 4983230072969 + 3 ^ 40 * 1342938 * 2
def baseEnd_1342938 : Nat := 459715122125181321732631

theorem tailTrace_1342938 : CollatzResearch.WordTrace tailWord_1342938 prefixEnd_1342938 459715122125181321732631 := by
  unfold tailWord_1342938
  simp only [CollatzResearch.WordTrace]
  refine ⟨12245243202193114098895367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32653981872514970930387645 12245243202193114098895367)
  ·
    refine ⟨18367864803289671148343051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12245243202193114098895367 18367864803289671148343051)
    ·
      refine ⟨27551797204934506722514577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18367864803289671148343051 27551797204934506722514577)
      ·
        refine ⟨20663847903700880041885933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27551797204934506722514577 20663847903700880041885933)
        ·
          refine ⟨7748942963887830015707225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20663847903700880041885933 7748942963887830015707225)
          ·
            refine ⟨5811707222915872511780419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7748942963887830015707225 5811707222915872511780419)
            ·
              refine ⟨8717560834373808767670629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5811707222915872511780419 8717560834373808767670629)
              ·
                refine ⟨1634542656445089143938243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8717560834373808767670629 1634542656445089143938243)
                ·
                  refine ⟨2451813984667633715907365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1634542656445089143938243 2451813984667633715907365)
                  ·
                    refine ⟨459715122125181321732631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2451813984667633715907365 459715122125181321732631)
                    ·
                      rfl

theorem cell22_1342938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 4, 1, 4].length) (baseStart_1342938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1342938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1342938 prefixEnd_1342938 := by exact prefixLift 1342938
  have htrace : WordTrace (prefixWord ++ tailWord_1342938) baseStart_1342938 baseEnd_1342938 := by
    simpa [prefixWord, tailWord_1342938, baseEnd_1342938] using wordTrace_append hprefix tailTrace_1342938
  have hstable : (prefixWord ++ tailWord_1342938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342938).length < 2 ^ (prefixWord ++ tailWord_1342938).sum := by decide
  have hdescent : baseEnd_1342938 < baseStart_1342938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342968 : List Nat := [2, 1, 2, 1, 1, 5, 2, 1, 4, 3]
def baseStart_1342968 : Nat := 118140960795 + 1342968 * 2 ^ 59
def prefixEnd_1342968 : Nat := 4983230072969 + 3 ^ 40 * 1342968 * 2
def baseEnd_1342968 : Nat := 459725391738271243482539

theorem tailTrace_1342968 : CollatzResearch.WordTrace tailWord_1342968 prefixEnd_1342968 459725391738271243482539 := by
  unfold tailWord_1342968
  simp only [CollatzResearch.WordTrace]
  refine ⟨24491033499331885759586779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32654711332442514346115705 24491033499331885759586779)
  ·
    refine ⟨36736550248997828639380169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24491033499331885759586779 36736550248997828639380169)
    ·
      refine ⟨27552412686748371479535127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36736550248997828639380169 27552412686748371479535127)
      ·
        refine ⟨41328619030122557219302691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27552412686748371479535127 41328619030122557219302691)
        ·
          refine ⟨61992928545183835828954037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41328619030122557219302691 61992928545183835828954037)
          ·
            refine ⟨5811837051110984608964441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61992928545183835828954037 5811837051110984608964441)
            ·
              refine ⟨4358877788333238456723331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5811837051110984608964441 4358877788333238456723331)
              ·
                refine ⟨6538316682499857685084997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4358877788333238456723331 6538316682499857685084997)
                ·
                  refine ⟨1225934377968723315953437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6538316682499857685084997 1225934377968723315953437)
                  ·
                    refine ⟨459725391738271243482539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1225934377968723315953437 459725391738271243482539)
                    ·
                      rfl

theorem cell22_1342968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 4, 3].length) (baseStart_1342968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1342968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1342968 prefixEnd_1342968 := by exact prefixLift 1342968
  have htrace : WordTrace (prefixWord ++ tailWord_1342968) baseStart_1342968 baseEnd_1342968 := by
    simpa [prefixWord, tailWord_1342968, baseEnd_1342968] using wordTrace_append hprefix tailTrace_1342968
  have hstable : (prefixWord ++ tailWord_1342968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342968).length < 2 ^ (prefixWord ++ tailWord_1342968).sum := by decide
  have hdescent : baseEnd_1342968 < baseStart_1342968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342970 : List Nat := [3, 1, 1, 1, 1, 2, 7, 2, 4]
def baseStart_1342970 : Nat := 118140960795 + 1342970 * 2 ^ 59
def prefixEnd_1342970 : Nat := 4983230072969 + 3 ^ 40 * 1342970 * 2
def baseEnd_1342970 : Nat := 153242025459714634977511

theorem tailTrace_1342970 : CollatzResearch.WordTrace tailWord_1342970 prefixEnd_1342970 153242025459714634977511 := by
  unfold tailWord_1342970
  simp only [CollatzResearch.WordTrace]
  refine ⟨12245534986164131465186591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32654759963104350573830909 12245534986164131465186591)
  ·
    refine ⟨18368302479246197197779887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12245534986164131465186591 18368302479246197197779887)
    ·
      refine ⟨27552453718869295796669831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18368302479246197197779887 27552453718869295796669831)
      ·
        refine ⟨41328680578303943695004747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27552453718869295796669831 41328680578303943695004747)
        ·
          refine ⟨61993020867455915542507121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41328680578303943695004747 61993020867455915542507121)
          ·
            refine ⟨46494765650591936656880341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61993020867455915542507121 46494765650591936656880341)
            ·
              refine ⟨1089721069935748515395633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 46494765650591936656880341 1089721069935748515395633)
              ·
                refine ⟨817290802451811386546725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1089721069935748515395633 817290802451811386546725)
                ·
                  refine ⟨153242025459714634977511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 817290802451811386546725 153242025459714634977511)
                  ·
                    rfl

theorem cell22_1342970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7, 2, 4].length) (baseStart_1342970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1342970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1342970 prefixEnd_1342970 := by exact prefixLift 1342970
  have htrace : WordTrace (prefixWord ++ tailWord_1342970) baseStart_1342970 baseEnd_1342970 := by
    simpa [prefixWord, tailWord_1342970, baseEnd_1342970] using wordTrace_append hprefix tailTrace_1342970
  have hstable : (prefixWord ++ tailWord_1342970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342970).length < 2 ^ (prefixWord ++ tailWord_1342970).sum := by decide
  have hdescent : baseEnd_1342970 < baseStart_1342970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343000 : List Nat := [2, 1, 2, 3, 4, 1, 2, 1, 2, 4]
def baseStart_1343000 : Nat := 118140960795 + 1343000 * 2 ^ 59
def prefixEnd_1343000 : Nat := 4983230072969 + 3 ^ 40 * 1343000 * 2
def baseEnd_1343000 : Nat := 459736345992233826682441

theorem tailTrace_1343000 : CollatzResearch.WordTrace tailWord_1343000 prefixEnd_1343000 459736345992233826682441 := by
  unfold tailWord_1343000
  simp only [CollatzResearch.WordTrace]
  refine ⟨24491617067273920492169227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32655489423031893989558969 24491617067273920492169227)
  ·
    refine ⟨36737425600910880738253841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24491617067273920492169227 36737425600910880738253841)
    ·
      refine ⟨27553069200683160553690381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36737425600910880738253841 27553069200683160553690381)
      ·
        refine ⟨10332400950256185207633893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27553069200683160553690381 10332400950256185207633893)
        ·
          refine ⟨1937325178173034726431355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10332400950256185207633893 1937325178173034726431355)
          ·
            refine ⟨2905987767259552089647033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1937325178173034726431355 2905987767259552089647033)
            ·
              refine ⟨2179490825444664067235275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2905987767259552089647033 2179490825444664067235275)
              ·
                refine ⟨3269236238166996100852913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2179490825444664067235275 3269236238166996100852913)
                ·
                  refine ⟨2451927178625247075639685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3269236238166996100852913 2451927178625247075639685)
                  ·
                    refine ⟨459736345992233826682441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2451927178625247075639685 459736345992233826682441)
                    ·
                      rfl

theorem cell22_1343000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 1, 2, 4].length) (baseStart_1343000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1343000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1343000 prefixEnd_1343000 := by exact prefixLift 1343000
  have htrace : WordTrace (prefixWord ++ tailWord_1343000) baseStart_1343000 baseEnd_1343000 := by
    simpa [prefixWord, tailWord_1343000, baseEnd_1343000] using wordTrace_append hprefix tailTrace_1343000
  have hstable : (prefixWord ++ tailWord_1343000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343000).length < 2 ^ (prefixWord ++ tailWord_1343000).sum := by decide
  have hdescent : baseEnd_1343000 < baseStart_1343000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343088 : List Nat := [2, 1, 1, 1, 6, 1, 1, 3, 6]
def baseStart_1343088 : Nat := 118140960795 + 1343088 * 2 ^ 59
def prefixEnd_1343088 : Nat := 4983230072969 + 3 ^ 40 * 1343088 * 2
def baseEnd_1343088 : Nat := 153255490063543643494057

theorem tailTrace_1343088 : CollatzResearch.WordTrace tailWord_1343088 prefixEnd_1343088 153255490063543643494057 := by
  unfold tailWord_1343088
  simp only [CollatzResearch.WordTrace]
  refine ⟨24493221879114516006770959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32657629172152688009027945 24493221879114516006770959)
  ·
    refine ⟨36739832818671774010156439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24493221879114516006770959 36739832818671774010156439)
    ·
      refine ⟨55109749228007661015234659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36739832818671774010156439 55109749228007661015234659)
      ·
        refine ⟨82664623842011491522851989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55109749228007661015234659 82664623842011491522851989)
        ·
          refine ⟨3874904242594288665133687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 82664623842011491522851989 3874904242594288665133687)
          ·
            refine ⟨5812356363891432997700531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3874904242594288665133687 5812356363891432997700531)
            ·
              refine ⟨8718534545837149496550797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5812356363891432997700531 8718534545837149496550797)
              ·
                refine ⟨3269450454688931061206549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8718534545837149496550797 3269450454688931061206549)
                ·
                  refine ⟨153255490063543643494057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3269450454688931061206549 153255490063543643494057)
                  ·
                    rfl

theorem cell22_1343088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 3, 6].length) (baseStart_1343088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1343088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1343088 prefixEnd_1343088 := by exact prefixLift 1343088
  have htrace : WordTrace (prefixWord ++ tailWord_1343088) baseStart_1343088 baseEnd_1343088 := by
    simpa [prefixWord, tailWord_1343088, baseEnd_1343088] using wordTrace_append hprefix tailTrace_1343088
  have hstable : (prefixWord ++ tailWord_1343088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343088).length < 2 ^ (prefixWord ++ tailWord_1343088).sum := by decide
  have hdescent : baseEnd_1343088 < baseStart_1343088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343165 : List Nat := [1, 4, 1, 2, 1, 2, 2, 1, 5, 3]
def baseStart_1343165 : Nat := 118140960795 + 1343165 * 2 ^ 59
def prefixEnd_1343165 : Nat := 4983230072969 + 3 ^ 40 * 1343165 * 2
def baseEnd_1343165 : Nat := 459792828864228396306935

theorem tailTrace_1343165 : CollatzResearch.WordTrace tailWord_1343165 prefixEnd_1343165 459792828864228396306935 := by
  unfold tailWord_1343165
  simp only [CollatzResearch.WordTrace]
  refine ⟨48989252178950074164094949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32659501452633382776063299 48989252178950074164094949)
  ·
    refine ⟨9185484783553138905767803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48989252178950074164094949 9185484783553138905767803)
    ·
      refine ⟨13778227175329708358651705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9185484783553138905767803 13778227175329708358651705)
      ·
        refine ⟨10333670381497281268988779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13778227175329708358651705 10333670381497281268988779)
        ·
          refine ⟨15500505572245921903483169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10333670381497281268988779 15500505572245921903483169)
          ·
            refine ⟨11625379179184441427612377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15500505572245921903483169 11625379179184441427612377)
            ·
              refine ⟨8719034384388331070709283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11625379179184441427612377 8719034384388331070709283)
              ·
                refine ⟨13078551576582496606063925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8719034384388331070709283 13078551576582496606063925)
                ·
                  refine ⟨1226114210304609056818493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13078551576582496606063925 1226114210304609056818493)
                  ·
                    refine ⟨459792828864228396306935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1226114210304609056818493 459792828864228396306935)
                    ·
                      rfl

theorem cell22_1343165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 5, 3].length) (baseStart_1343165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1343165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1343165 prefixEnd_1343165 := by exact prefixLift 1343165
  have htrace : WordTrace (prefixWord ++ tailWord_1343165) baseStart_1343165 baseEnd_1343165 := by
    simpa [prefixWord, tailWord_1343165, baseEnd_1343165] using wordTrace_append hprefix tailTrace_1343165
  have hstable : (prefixWord ++ tailWord_1343165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343165).length < 2 ^ (prefixWord ++ tailWord_1343165).sum := by decide
  have hdescent : baseEnd_1343165 < baseStart_1343165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343190 : List Nat := [5, 2, 1, 3, 2, 1, 2, 2, 4]
def baseStart_1343190 : Nat := 118140960795 + 1343190 * 2 ^ 59
def prefixEnd_1343190 : Nat := 4983230072969 + 3 ^ 40 * 1343190 * 2
def baseEnd_1343190 : Nat := 153267128958378888143953

theorem tailTrace_1343190 : CollatzResearch.WordTrace tailWord_1343190 prefixEnd_1343190 153267128958378888143953 := by
  unfold tailWord_1343190
  simp only [CollatzResearch.WordTrace]
  refine ⟨3061885250241218964609689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32660109335906335622503349 3061885250241218964609689)
  ·
    refine ⟨2296413937680914223457267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3061885250241218964609689 2296413937680914223457267)
    ·
      refine ⟨3444620906521371335185901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2296413937680914223457267 3444620906521371335185901)
      ·
        refine ⟨1291732839945514250694713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3444620906521371335185901 1291732839945514250694713)
        ·
          refine ⟨968799629959135688021035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1291732839945514250694713 968799629959135688021035)
          ·
            refine ⟨1453199444938703532031553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 968799629959135688021035 1453199444938703532031553)
            ·
              refine ⟨1089899583704027649023665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1453199444938703532031553 1089899583704027649023665)
              ·
                refine ⟨817424687778020736767749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1089899583704027649023665 817424687778020736767749)
                ·
                  refine ⟨153267128958378888143953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 817424687778020736767749 153267128958378888143953)
                  ·
                    rfl

theorem cell22_1343190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_1343190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1343190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1343190 prefixEnd_1343190 := by exact prefixLift 1343190
  have htrace : WordTrace (prefixWord ++ tailWord_1343190) baseStart_1343190 baseEnd_1343190 := by
    simpa [prefixWord, tailWord_1343190, baseEnd_1343190] using wordTrace_append hprefix tailTrace_1343190
  have hstable : (prefixWord ++ tailWord_1343190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343190).length < 2 ^ (prefixWord ++ tailWord_1343190).sum := by decide
  have hdescent : baseEnd_1343190 < baseStart_1343190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343223 : List Nat := [1, 1, 3, 1, 1, 1, 5, 1, 8]
def baseStart_1343223 : Nat := 118140960795 + 1343223 * 2 ^ 59
def prefixEnd_1343223 : Nat := 4983230072969 + 3 ^ 40 * 1343223 * 2
def baseEnd_1343223 : Nat := 153270894483178526118919

theorem tailTrace_1343223 : CollatzResearch.WordTrace tailWord_1343223 prefixEnd_1343223 153270894483178526118919 := by
  unfold tailWord_1343223
  simp only [CollatzResearch.WordTrace]
  refine ⟨48991367612739950069706323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32660911741826633379804215 48991367612739950069706323)
  ·
    refine ⟨73487051419109925104559485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48991367612739950069706323 73487051419109925104559485)
    ·
      refine ⟨27557644282166221914209807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73487051419109925104559485 27557644282166221914209807)
      ·
        refine ⟨41336466423249332871314711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27557644282166221914209807 41336466423249332871314711)
        ·
          refine ⟨62004699634873999306972067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41336466423249332871314711 62004699634873999306972067)
          ·
            refine ⟨93007049452310998960458101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62004699634873999306972067 93007049452310998960458101)
            ·
              refine ⟨8719410886154156152542947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 93007049452310998960458101 8719410886154156152542947)
              ·
                refine ⟨13079116329231234228814421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8719410886154156152542947 13079116329231234228814421)
                ·
                  refine ⟨153270894483178526118919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13079116329231234228814421 153270894483178526118919)
                  ·
                    rfl

theorem cell22_1343223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 8].length) (baseStart_1343223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1343223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1343223 prefixEnd_1343223 := by exact prefixLift 1343223
  have htrace : WordTrace (prefixWord ++ tailWord_1343223) baseStart_1343223 baseEnd_1343223 := by
    simpa [prefixWord, tailWord_1343223, baseEnd_1343223] using wordTrace_append hprefix tailTrace_1343223
  have hstable : (prefixWord ++ tailWord_1343223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343223).length < 2 ^ (prefixWord ++ tailWord_1343223).sum := by decide
  have hdescent : baseEnd_1343223 < baseStart_1343223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343242 : List Nat := [3, 1, 2, 2, 1, 4, 1, 3, 1, 4]
def baseStart_1343242 : Nat := 118140960795 + 1343242 * 2 ^ 59
def prefixEnd_1343242 : Nat := 4983230072969 + 3 ^ 40 * 1343242 * 2
def baseEnd_1343242 : Nat := 459819187537825862131699

theorem tailTrace_1343242 : CollatzResearch.WordTrace tailWord_1343242 prefixEnd_1343242 459819187537825862131699 := by
  unfold tailWord_1343242
  simp only [CollatzResearch.WordTrace]
  refine ⟨12248015149917779078661995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32661373733114077543098653 12248015149917779078661995)
  ·
    refine ⟨18372022724876668617992993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12248015149917779078661995 18372022724876668617992993)
    ·
      refine ⟨13779017043657501463494745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18372022724876668617992993 13779017043657501463494745)
      ·
        refine ⟨10334262782743126097621059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13779017043657501463494745 10334262782743126097621059)
        ·
          refine ⟨15501394174114689146431589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10334262782743126097621059 15501394174114689146431589)
          ·
            refine ⟨2906511407646504214955923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15501394174114689146431589 2906511407646504214955923)
            ·
              refine ⟨4359767111469756322433885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2906511407646504214955923 4359767111469756322433885)
              ·
                refine ⟨1634912666801158620912707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4359767111469756322433885 1634912666801158620912707)
                ·
                  refine ⟨2452369000201737931369061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1634912666801158620912707 2452369000201737931369061)
                  ·
                    refine ⟨459819187537825862131699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2452369000201737931369061 459819187537825862131699)
                    ·
                      rfl

theorem cell22_1343242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 3, 1, 4].length) (baseStart_1343242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1343242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1343242 prefixEnd_1343242 := by exact prefixLift 1343242
  have htrace : WordTrace (prefixWord ++ tailWord_1343242) baseStart_1343242 baseEnd_1343242 := by
    simpa [prefixWord, tailWord_1343242, baseEnd_1343242] using wordTrace_append hprefix tailTrace_1343242
  have hstable : (prefixWord ++ tailWord_1343242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343242).length < 2 ^ (prefixWord ++ tailWord_1343242).sum := by decide
  have hdescent : baseEnd_1343242 < baseStart_1343242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343272 : List Nat := [2, 1, 5, 1, 1, 2, 3, 1, 1, 5]
def baseStart_1343272 : Nat := 118140960795 + 1343272 * 2 ^ 59
def prefixEnd_1343272 : Nat := 4983230072969 + 3 ^ 40 * 1343272 * 2
def baseEnd_1343272 : Nat := 459829457150915783881607

theorem tailTrace_1343272 : CollatzResearch.WordTrace tailWord_1343272 prefixEnd_1343272 459829457150915783881607 := by
  unfold tailWord_1343272
  simp only [CollatzResearch.WordTrace]
  refine ⟨24496577394781215719120035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32662103193041620958826713 24496577394781215719120035)
  ·
    refine ⟨36744866092171823578680053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24496577394781215719120035 36744866092171823578680053)
    ·
      refine ⟨3444831196141108460501255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36744866092171823578680053 3444831196141108460501255)
      ·
        refine ⟨5167246794211662690751883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3444831196141108460501255 5167246794211662690751883)
        ·
          refine ⟨7750870191317494036127825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5167246794211662690751883 7750870191317494036127825)
          ·
            refine ⟨5813152643488120527095869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7750870191317494036127825 5813152643488120527095869)
            ·
              refine ⟨2179932241308045197660951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5813152643488120527095869 2179932241308045197660951)
              ·
                refine ⟨3269898361962067796491427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2179932241308045197660951 3269898361962067796491427)
                ·
                  refine ⟨4904847542943101694737141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3269898361962067796491427 4904847542943101694737141)
                  ·
                    refine ⟨459829457150915783881607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4904847542943101694737141 459829457150915783881607)
                    ·
                      rfl

theorem cell22_1343272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_1343272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1343272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1343272 prefixEnd_1343272 := by exact prefixLift 1343272
  have htrace : WordTrace (prefixWord ++ tailWord_1343272) baseStart_1343272 baseEnd_1343272 := by
    simpa [prefixWord, tailWord_1343272, baseEnd_1343272] using wordTrace_append hprefix tailTrace_1343272
  have hstable : (prefixWord ++ tailWord_1343272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343272).length < 2 ^ (prefixWord ++ tailWord_1343272).sum := by decide
  have hdescent : baseEnd_1343272 < baseStart_1343272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343407 : List Nat := [1, 1, 2, 1, 2, 2, 4, 2, 4, 3]
def baseStart_1343407 : Nat := 118140960795 + 1343407 * 2 ^ 59
def prefixEnd_1343407 : Nat := 4983230072969 + 3 ^ 40 * 1343407 * 2
def baseEnd_1343407 : Nat := 459875670409820431756193

theorem tailTrace_1343407 : CollatzResearch.WordTrace tailWord_1343407 prefixEnd_1343407 459875670409820431756193 := by
  unfold tailWord_1343407
  simp only [CollatzResearch.WordTrace]
  refine ⟨48998078644073349494404475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32665385762715566329602983 48998078644073349494404475)
  ·
    refine ⟨73497117966110024241606713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48998078644073349494404475 73497117966110024241606713)
    ·
      refine ⟨55122838474582518181205035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73497117966110024241606713 55122838474582518181205035)
      ·
        refine ⟨82684257711873777271807553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55122838474582518181205035 82684257711873777271807553)
        ·
          refine ⟨62013193283905332953855665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82684257711873777271807553 62013193283905332953855665)
          ·
            refine ⟨46509894962928999715391749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62013193283905332953855665 46509894962928999715391749)
            ·
              refine ⟨8720605305549187446635953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46509894962928999715391749 8720605305549187446635953)
              ·
                refine ⟨6540453979161890584976965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8720605305549187446635953 6540453979161890584976965)
                ·
                  refine ⟨1226335121092854484683181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6540453979161890584976965 1226335121092854484683181)
                  ·
                    refine ⟨459875670409820431756193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1226335121092854484683181 459875670409820431756193)
                    ·
                      rfl

theorem cell22_1343407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 4, 3].length) (baseStart_1343407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1343407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1343407 prefixEnd_1343407 := by exact prefixLift 1343407
  have htrace : WordTrace (prefixWord ++ tailWord_1343407) baseStart_1343407 baseEnd_1343407 := by
    simpa [prefixWord, tailWord_1343407, baseEnd_1343407] using wordTrace_append hprefix tailTrace_1343407
  have hstable : (prefixWord ++ tailWord_1343407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343407).length < 2 ^ (prefixWord ++ tailWord_1343407).sum := by decide
  have hdescent : baseEnd_1343407 < baseStart_1343407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343409 : List Nat := [1, 2, 2, 4, 2, 1, 1, 5, 4]
def baseStart_1343409 : Nat := 118140960795 + 1343409 * 2 ^ 59
def prefixEnd_1343409 : Nat := 4983230072969 + 3 ^ 40 * 1343409 * 2
def baseEnd_1343409 : Nat := 153292118350231031068729

theorem tailTrace_1343409 : CollatzResearch.WordTrace tailWord_1343409 prefixEnd_1343409 153292118350231031068729 := by
  unfold tailWord_1343409
  simp only [CollatzResearch.WordTrace]
  refine ⟨48998151590066103835977281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32665434393377402557318187 48998151590066103835977281)
  ·
    refine ⟨36748613692549577876982961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48998151590066103835977281 36748613692549577876982961)
    ·
      refine ⟨27561460269412183407737221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36748613692549577876982961 27561460269412183407737221)
      ·
        refine ⟨5167773800514784388950729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27561460269412183407737221 5167773800514784388950729)
        ·
          refine ⟨3875830350386088291713047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5167773800514784388950729 3875830350386088291713047)
          ·
            refine ⟨5813745525579132437569571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3875830350386088291713047 5813745525579132437569571)
            ·
              refine ⟨8720618288368698656354357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5813745525579132437569571 8720618288368698656354357)
              ·
                refine ⟨817557964534565499033221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8720618288368698656354357 817557964534565499033221)
                ·
                  refine ⟨153292118350231031068729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 817557964534565499033221 153292118350231031068729)
                  ·
                    rfl

theorem cell22_1343409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 5, 4].length) (baseStart_1343409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1343409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1343409 prefixEnd_1343409 := by exact prefixLift 1343409
  have htrace : WordTrace (prefixWord ++ tailWord_1343409) baseStart_1343409 baseEnd_1343409 := by
    simpa [prefixWord, tailWord_1343409, baseEnd_1343409] using wordTrace_append hprefix tailTrace_1343409
  have hstable : (prefixWord ++ tailWord_1343409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343409).length < 2 ^ (prefixWord ++ tailWord_1343409).sum := by decide
  have hdescent : baseEnd_1343409 < baseStart_1343409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343492 : List Nat := [2, 3, 2, 4, 2, 1, 2, 1, 2, 3]
def baseStart_1343492 : Nat := 118140960795 + 1343492 * 2 ^ 59
def prefixEnd_1343492 : Nat := 4983230072969 + 3 ^ 40 * 1343492 * 2
def baseEnd_1343492 : Nat := 459904767646908543380933

theorem tailTrace_1343492 : CollatzResearch.WordTrace tailWord_1343492 prefixEnd_1343492 459904767646908543380933 := by
  unfold tailWord_1343492
  simp only [CollatzResearch.WordTrace]
  refine ⟨24500589424382704505624365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32667452565843606007499153 24500589424382704505624365)
  ·
    refine ⟨9187721034143514189609137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24500589424382704505624365 9187721034143514189609137)
    ·
      refine ⟨6890790775607635642206853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9187721034143514189609137 6890790775607635642206853)
      ·
        refine ⟨1292023270426431682913785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6890790775607635642206853 1292023270426431682913785)
        ·
          refine ⟨969017452819823762185339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1292023270426431682913785 969017452819823762185339)
          ·
            refine ⟨1453526179229735643278009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 969017452819823762185339 1453526179229735643278009)
            ·
              refine ⟨1090144634422301732458507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1453526179229735643278009 1090144634422301732458507)
              ·
                refine ⟨1635216951633452598687761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1090144634422301732458507 1635216951633452598687761)
                ·
                  refine ⟨1226412713725089449015821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1635216951633452598687761 1226412713725089449015821)
                  ·
                    refine ⟨459904767646908543380933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1226412713725089449015821 459904767646908543380933)
                    ·
                      rfl

theorem cell22_1343492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 2, 1, 2, 3].length) (baseStart_1343492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1343492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1343492 prefixEnd_1343492 := by exact prefixLift 1343492
  have htrace : WordTrace (prefixWord ++ tailWord_1343492) baseStart_1343492 baseEnd_1343492 := by
    simpa [prefixWord, tailWord_1343492, baseEnd_1343492] using wordTrace_append hprefix tailTrace_1343492
  have hstable : (prefixWord ++ tailWord_1343492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343492).length < 2 ^ (prefixWord ++ tailWord_1343492).sum := by decide
  have hdescent : baseEnd_1343492 < baseStart_1343492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343557 : List Nat := [1, 3, 1, 1, 1, 3, 1, 4, 1, 6]
def baseStart_1343557 : Nat := 118140960795 + 1343557 * 2 ^ 59
def prefixEnd_1343557 : Nat := 4983230072969 + 3 ^ 40 * 1343557 * 2
def baseEnd_1343557 : Nat := 459927018475270040505733

theorem tailTrace_1343557 : CollatzResearch.WordTrace tailWord_1343557 prefixEnd_1343557 459927018475270040505733 := by
  unfold tailWord_1343557
  simp only [CollatzResearch.WordTrace]
  refine ⟨49003549593529925112364925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32669033062353283408243283 49003549593529925112364925)
  ·
    refine ⟨18376331097573721917136847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49003549593529925112364925 18376331097573721917136847)
    ·
      refine ⟨27564496646360582875705271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18376331097573721917136847 27564496646360582875705271)
      ·
        refine ⟨41346744969540874313557907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27564496646360582875705271 41346744969540874313557907)
        ·
          refine ⟨62020117454311311470336861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41346744969540874313557907 62020117454311311470336861)
          ·
            refine ⟨23257544045366741801376323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62020117454311311470336861 23257544045366741801376323)
            ·
              refine ⟨34886316068050112702064485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23257544045366741801376323 34886316068050112702064485)
              ·
                refine ⟨6541184262759396131637091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34886316068050112702064485 6541184262759396131637091)
                ·
                  refine ⟨9811776394139094197455637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6541184262759396131637091 9811776394139094197455637)
                  ·
                    refine ⟨459927018475270040505733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9811776394139094197455637 459927018475270040505733)
                    ·
                      rfl

theorem cell22_1343557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 6].length) (baseStart_1343557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1343557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1343557 prefixEnd_1343557 := by exact prefixLift 1343557
  have htrace : WordTrace (prefixWord ++ tailWord_1343557) baseStart_1343557 baseEnd_1343557 := by
    simpa [prefixWord, tailWord_1343557, baseEnd_1343557] using wordTrace_append hprefix tailTrace_1343557
  have hstable : (prefixWord ++ tailWord_1343557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343557).length < 2 ^ (prefixWord ++ tailWord_1343557).sum := by decide
  have hdescent : baseEnd_1343557 < baseStart_1343557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343559 : List Nat := [1, 1, 4, 1, 3, 1, 4, 1, 1, 5]
def baseStart_1343559 : Nat := 118140960795 + 1343559 * 2 ^ 59
def prefixEnd_1343559 : Nat := 4983230072969 + 3 ^ 40 * 1343559 * 2
def baseEnd_1343559 : Nat := 459927703116142701955727

theorem tailTrace_1343559 : CollatzResearch.WordTrace tailWord_1343559 prefixEnd_1343559 459927703116142701955727 := by
  unfold tailWord_1343559
  simp only [CollatzResearch.WordTrace]
  refine ⟨49003622539522679453937731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32669081693015119635958487 49003622539522679453937731)
  ·
    refine ⟨73505433809284019180906597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49003622539522679453937731 73505433809284019180906597)
    ·
      refine ⟨13782268839240753596419987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73505433809284019180906597 13782268839240753596419987)
      ·
        refine ⟨20673403258861130394629981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13782268839240753596419987 20673403258861130394629981)
        ·
          refine ⟨7752526222072923897986243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20673403258861130394629981 7752526222072923897986243)
          ·
            refine ⟨11628789333109385846979365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7752526222072923897986243 11628789333109385846979365)
            ·
              refine ⟨2180397999958009846308631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11628789333109385846979365 2180397999958009846308631)
              ·
                refine ⟨3270596999937014769462947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2180397999958009846308631 3270596999937014769462947)
                ·
                  refine ⟨4905895499905522154194421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3270596999937014769462947 4905895499905522154194421)
                  ·
                    refine ⟨459927703116142701955727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4905895499905522154194421 459927703116142701955727)
                    ·
                      rfl

theorem cell22_1343559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 1, 1, 5].length) (baseStart_1343559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1343559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1343559 prefixEnd_1343559 := by exact prefixLift 1343559
  have htrace : WordTrace (prefixWord ++ tailWord_1343559) baseStart_1343559 baseEnd_1343559 := by
    simpa [prefixWord, tailWord_1343559, baseEnd_1343559] using wordTrace_append hprefix tailTrace_1343559
  have hstable : (prefixWord ++ tailWord_1343559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343559).length < 2 ^ (prefixWord ++ tailWord_1343559).sum := by decide
  have hdescent : baseEnd_1343559 < baseStart_1343559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343621 : List Nat := [1, 3, 1, 1, 5, 1, 2, 2, 3, 3]
def baseStart_1343621 : Nat := 118140960795 + 1343621 * 2 ^ 59
def prefixEnd_1343621 : Nat := 4983230072969 + 3 ^ 40 * 1343621 * 2
def baseEnd_1343621 : Nat := 459948926983195206905537

theorem tailTrace_1343621 : CollatzResearch.WordTrace tailWord_1343621 prefixEnd_1343621 459948926983195206905537 := by
  unfold tailWord_1343621
  simp only [CollatzResearch.WordTrace]
  refine ⟨49005883865298064042694717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32670589243532042695129811 49005883865298064042694717)
  ·
    refine ⟨18377206449486774016010519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49005883865298064042694717 18377206449486774016010519)
    ·
      refine ⟨27565809674230161024015779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18377206449486774016010519 27565809674230161024015779)
      ·
        refine ⟨41348714511345241536023669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27565809674230161024015779 41348714511345241536023669)
        ·
          refine ⟨3876441985438616394002219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41348714511345241536023669 3876441985438616394002219)
          ·
            refine ⟨5814662978157924591003329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3876441985438616394002219 5814662978157924591003329)
            ·
              refine ⟨4360997233618443443252497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5814662978157924591003329 4360997233618443443252497)
              ·
                refine ⟨3270747925213832582439373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4360997233618443443252497 3270747925213832582439373)
                ·
                  refine ⟨1226530471955187218414765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3270747925213832582439373 1226530471955187218414765)
                  ·
                    refine ⟨459948926983195206905537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1226530471955187218414765 459948926983195206905537)
                    ·
                      rfl

theorem cell22_1343621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 2, 3, 3].length) (baseStart_1343621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1343621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1343621 prefixEnd_1343621 := by exact prefixLift 1343621
  have htrace : WordTrace (prefixWord ++ tailWord_1343621) baseStart_1343621 baseEnd_1343621 := by
    simpa [prefixWord, tailWord_1343621, baseEnd_1343621] using wordTrace_append hprefix tailTrace_1343621
  have hstable : (prefixWord ++ tailWord_1343621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343621).length < 2 ^ (prefixWord ++ tailWord_1343621).sum := by decide
  have hdescent : baseEnd_1343621 < baseStart_1343621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343634 : List Nat := [3, 2, 3, 1, 1, 1, 1, 1, 9]
def baseStart_1343634 : Nat := 118140960795 + 1343634 * 2 ^ 59
def prefixEnd_1343634 : Nat := 4983230072969 + 3 ^ 40 * 1343634 * 2
def baseEnd_1343634 : Nat := 153317792382955835443499

theorem tailTrace_1343634 : CollatzResearch.WordTrace tailWord_1343634 prefixEnd_1343634 153317792382955835443499 := by
  unfold tailWord_1343634
  simp only [CollatzResearch.WordTrace]
  refine ⟨12251589503562741815729489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32670905342833978175278637 12251589503562741815729489)
  ·
    refine ⟨9188692127672056361797117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12251589503562741815729489 9188692127672056361797117)
    ·
      refine ⟨3445759547877021135673919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9188692127672056361797117 3445759547877021135673919)
      ·
        refine ⟨5168639321815531703510879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3445759547877021135673919 5168639321815531703510879)
        ·
          refine ⟨7752958982723297555266319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5168639321815531703510879 7752958982723297555266319)
          ·
            refine ⟨11629438474084946332899479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7752958982723297555266319 11629438474084946332899479)
            ·
              refine ⟨17444157711127419499349219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11629438474084946332899479 17444157711127419499349219)
              ·
                refine ⟨26166236566691129249023829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17444157711127419499349219 26166236566691129249023829)
                ·
                  refine ⟨153317792382955835443499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 26166236566691129249023829 153317792382955835443499)
                  ·
                    rfl

theorem cell22_1343634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 9].length) (baseStart_1343634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1343634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1343634 prefixEnd_1343634 := by exact prefixLift 1343634
  have htrace : WordTrace (prefixWord ++ tailWord_1343634) baseStart_1343634 baseEnd_1343634 := by
    simpa [prefixWord, tailWord_1343634, baseEnd_1343634] using wordTrace_append hprefix tailTrace_1343634
  have hstable : (prefixWord ++ tailWord_1343634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343634).length < 2 ^ (prefixWord ++ tailWord_1343634).sum := by decide
  have hdescent : baseEnd_1343634 < baseStart_1343634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343655 : List Nat := [1, 1, 6, 2, 2, 2, 1, 1, 3, 3]
def baseStart_1343655 : Nat := 118140960795 + 1343655 * 2 ^ 59
def prefixEnd_1343655 : Nat := 4983230072969 + 3 ^ 40 * 1343655 * 2
def baseEnd_1343655 : Nat := 459960565878030451555433

theorem tailTrace_1343655 : CollatzResearch.WordTrace tailWord_1343655 prefixEnd_1343655 459960565878030451555433 := by
  unfold tailWord_1343655
  simp only [CollatzResearch.WordTrace]
  refine ⟨49007123947174887849432419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32671415964783258566288279 49007123947174887849432419)
  ·
    refine ⟨73510685920762331774148629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49007123947174887849432419 73510685920762331774148629)
    ·
      refine ⟨3445813402535734301913217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 73510685920762331774148629 3445813402535734301913217)
      ·
        refine ⟨2584360051901800726434913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3445813402535734301913217 2584360051901800726434913)
        ·
          refine ⟨1938270038926350544826185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2584360051901800726434913 1938270038926350544826185)
          ·
            refine ⟨1453702529194762908619639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1938270038926350544826185 1453702529194762908619639)
            ·
              refine ⟨2180553793792144362929459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1453702529194762908619639 2180553793792144362929459)
              ·
                refine ⟨3270830690688216544394189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2180553793792144362929459 3270830690688216544394189)
                ·
                  refine ⟨1226561509008081204147821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3270830690688216544394189 1226561509008081204147821)
                  ·
                    refine ⟨459960565878030451555433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1226561509008081204147821 459960565878030451555433)
                    ·
                      rfl

theorem cell22_1343655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_1343655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1343655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1343655 prefixEnd_1343655 := by exact prefixLift 1343655
  have htrace : WordTrace (prefixWord ++ tailWord_1343655) baseStart_1343655 baseEnd_1343655 := by
    simpa [prefixWord, tailWord_1343655, baseEnd_1343655] using wordTrace_append hprefix tailTrace_1343655
  have hstable : (prefixWord ++ tailWord_1343655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343655).length < 2 ^ (prefixWord ++ tailWord_1343655).sum := by decide
  have hdescent : baseEnd_1343655 < baseStart_1343655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343756 : List Nat := [2, 2, 1, 2, 2, 2, 1, 2, 5, 3]
def baseStart_1343756 : Nat := 118140960795 + 1343756 * 2 ^ 59
def prefixEnd_1343756 : Nat := 4983230072969 + 3 ^ 40 * 1343756 * 2
def baseEnd_1343756 : Nat := 459995140242099854780123

theorem tailTrace_1343756 : CollatzResearch.WordTrace tailWord_1343756 prefixEnd_1343756 459995140242099854780123 := by
  unfold tailWord_1343756
  simp only [CollatzResearch.WordTrace]
  refine ⟨24505403859904491049429561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32673871813205988065906081 24505403859904491049429561)
  ·
    refine ⟨18379052894928368287072171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24505403859904491049429561 18379052894928368287072171)
    ·
      refine ⟨27568579342392552430608257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18379052894928368287072171 27568579342392552430608257)
      ·
        refine ⟨20676434506794414322956193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27568579342392552430608257 20676434506794414322956193)
        ·
          refine ⟨15507325880095810742217145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20676434506794414322956193 15507325880095810742217145)
          ·
            refine ⟨11630494410071858056662859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15507325880095810742217145 11630494410071858056662859)
            ·
              refine ⟨17445741615107787084994289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11630494410071858056662859 17445741615107787084994289)
              ·
                refine ⟨13084306211330840313745717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17445741615107787084994289 13084306211330840313745717)
                ·
                  refine ⟨1226653707312266279413661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13084306211330840313745717 1226653707312266279413661)
                  ·
                    refine ⟨459995140242099854780123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1226653707312266279413661 459995140242099854780123)
                    ·
                      rfl

theorem cell22_1343756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 5, 3].length) (baseStart_1343756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1343756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1343756 prefixEnd_1343756 := by exact prefixLift 1343756
  have htrace : WordTrace (prefixWord ++ tailWord_1343756) baseStart_1343756 baseEnd_1343756 := by
    simpa [prefixWord, tailWord_1343756, baseEnd_1343756] using wordTrace_append hprefix tailTrace_1343756
  have hstable : (prefixWord ++ tailWord_1343756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343756).length < 2 ^ (prefixWord ++ tailWord_1343756).sum := by decide
  have hdescent : baseEnd_1343756 < baseStart_1343756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343799 : List Nat := [1, 1, 3, 1, 2, 1, 1, 2, 2, 8]
def baseStart_1343799 : Nat := 118140960795 + 1343799 * 2 ^ 59
def prefixEnd_1343799 : Nat := 4983230072969 + 3 ^ 40 * 1343799 * 2
def baseEnd_1343799 : Nat := 460009860020862075954991

theorem tailTrace_1343799 : CollatzResearch.WordTrace tailWord_1343799 prefixEnd_1343799 460009860020862075954991 := by
  unfold tailWord_1343799
  simp only [CollatzResearch.WordTrace]
  refine ⟨49012376058653200442674451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32674917372435466961782967 49012376058653200442674451)
  ·
    refine ⟨73518564087979800664011677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49012376058653200442674451 73518564087979800664011677)
    ·
      refine ⟨27569461532992425249004379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73518564087979800664011677 27569461532992425249004379)
      ·
        refine ⟨41354192299488637873506569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27569461532992425249004379 41354192299488637873506569)
        ·
          refine ⟨31015644224616478405129927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41354192299488637873506569 31015644224616478405129927)
          ·
            refine ⟨46523466336924717607694891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31015644224616478405129927 46523466336924717607694891)
            ·
              refine ⟨69785199505387076411542337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46523466336924717607694891 69785199505387076411542337)
              ·
                refine ⟨52338899629040307308656753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69785199505387076411542337 52338899629040307308656753)
                ·
                  refine ⟨39254174721780230481492565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52338899629040307308656753 39254174721780230481492565)
                  ·
                    refine ⟨460009860020862075954991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 39254174721780230481492565 460009860020862075954991)
                    ·
                      rfl

theorem cell22_1343799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 8].length) (baseStart_1343799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1343799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1343799 prefixEnd_1343799 := by exact prefixLift 1343799
  have htrace : WordTrace (prefixWord ++ tailWord_1343799) baseStart_1343799 baseEnd_1343799 := by
    simpa [prefixWord, tailWord_1343799, baseEnd_1343799] using wordTrace_append hprefix tailTrace_1343799
  have hstable : (prefixWord ++ tailWord_1343799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343799).length < 2 ^ (prefixWord ++ tailWord_1343799).sum := by decide
  have hdescent : baseEnd_1343799 < baseStart_1343799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343850 : List Nat := [3, 1, 3, 3, 1, 1, 3, 2, 1, 4]
def baseStart_1343850 : Nat := 118140960795 + 1343850 * 2 ^ 59
def prefixEnd_1343850 : Nat := 4983230072969 + 3 ^ 40 * 1343850 * 2
def baseEnd_1343850 : Nat := 460027318363114942929835

theorem tailTrace_1343850 : CollatzResearch.WordTrace tailWord_1343850 prefixEnd_1343850 460027318363114942929835 := by
  unfold tailWord_1343850
  simp only [CollatzResearch.WordTrace]
  refine ⟨12253559045367109038195251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32676157454312290768520669 12253559045367109038195251)
  ·
    refine ⟨18380338568050663557292877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12253559045367109038195251 18380338568050663557292877)
    ·
      refine ⟨6892626963018998833984829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18380338568050663557292877 6892626963018998833984829)
      ·
        refine ⟨2584735111132124562744311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6892626963018998833984829 2584735111132124562744311)
        ·
          refine ⟨3877102666698186844116467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2584735111132124562744311 3877102666698186844116467)
          ·
            refine ⟨5815654000047280266174701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3877102666698186844116467 5815654000047280266174701)
            ·
              refine ⟨2180870250017730099815513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5815654000047280266174701 2180870250017730099815513)
              ·
                refine ⟨1635652687513297574861635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2180870250017730099815513 1635652687513297574861635)
                ·
                  refine ⟨2453479031269946362292453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1635652687513297574861635 2453479031269946362292453)
                  ·
                    refine ⟨460027318363114942929835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2453479031269946362292453 460027318363114942929835)
                    ·
                      rfl

theorem cell22_1343850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_1343850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1343850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1343850 prefixEnd_1343850 := by exact prefixLift 1343850
  have htrace : WordTrace (prefixWord ++ tailWord_1343850) baseStart_1343850 baseEnd_1343850 := by
    simpa [prefixWord, tailWord_1343850, baseEnd_1343850] using wordTrace_append hprefix tailTrace_1343850
  have hstable : (prefixWord ++ tailWord_1343850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343850).length < 2 ^ (prefixWord ++ tailWord_1343850).sum := by decide
  have hdescent : baseEnd_1343850 < baseStart_1343850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343880 : List Nat := [2, 1, 3, 3, 1, 1, 4, 2, 2, 3]
def baseStart_1343880 : Nat := 118140960795 + 1343880 * 2 ^ 59
def prefixEnd_1343880 : Nat := 4983230072969 + 3 ^ 40 * 1343880 * 2
def baseEnd_1343880 : Nat := 460037587976204864679743

theorem tailTrace_1343880 : CollatzResearch.WordTrace tailWord_1343880 prefixEnd_1343880 460037587976204864679743 := by
  unfold tailWord_1343880
  simp only [CollatzResearch.WordTrace]
  refine ⟨24507665185679875638186547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32676886914239834184248729 24507665185679875638186547)
  ·
    refine ⟨36761497778519813457279821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24507665185679875638186547 36761497778519813457279821)
    ·
      refine ⟨13785561666944930046479933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36761497778519813457279821 13785561666944930046479933)
      ·
        refine ⟨5169585625104348767429975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13785561666944930046479933 5169585625104348767429975)
        ·
          refine ⟨7754378437656523151144963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5169585625104348767429975 7754378437656523151144963)
          ·
            refine ⟨11631567656484784726717445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7754378437656523151144963 11631567656484784726717445)
            ·
              refine ⟨2180918935590897136259521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11631567656484784726717445 2180918935590897136259521)
              ·
                refine ⟨1635689201693172852194641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2180918935590897136259521 1635689201693172852194641)
                ·
                  refine ⟨1226766901269879639145981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1635689201693172852194641 1226766901269879639145981)
                  ·
                    refine ⟨460037587976204864679743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1226766901269879639145981 460037587976204864679743)
                    ·
                      rfl

theorem cell22_1343880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 2, 2, 3].length) (baseStart_1343880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1343880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1343880 prefixEnd_1343880 := by exact prefixLift 1343880
  have htrace : WordTrace (prefixWord ++ tailWord_1343880) baseStart_1343880 baseEnd_1343880 := by
    simpa [prefixWord, tailWord_1343880, baseEnd_1343880] using wordTrace_append hprefix tailTrace_1343880
  have hstable : (prefixWord ++ tailWord_1343880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343880).length < 2 ^ (prefixWord ++ tailWord_1343880).sum := by decide
  have hdescent : baseEnd_1343880 < baseStart_1343880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343882 : List Nat := [3, 1, 2, 5, 1, 1, 1, 4, 4]
def baseStart_1343882 : Nat := 118140960795 + 1343882 * 2 ^ 59
def prefixEnd_1343882 : Nat := 4983230072969 + 3 ^ 40 * 1343882 * 2
def baseEnd_1343882 : Nat := 153346090872359175376579

theorem tailTrace_1343882 : CollatzResearch.WordTrace tailWord_1343882 prefixEnd_1343882 153346090872359175376579 := by
  unfold tailWord_1343882
  simp only [CollatzResearch.WordTrace]
  refine ⟨12253850829338126404486475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32676935544901670411963933 12253850829338126404486475)
  ·
    refine ⟨18380776244007189606729713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12253850829338126404486475 18380776244007189606729713)
    ·
      refine ⟨13785582183005392205047285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18380776244007189606729713 13785582183005392205047285)
      ·
        refine ⟨1292398329656755519223183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13785582183005392205047285 1292398329656755519223183)
        ·
          refine ⟨1938597494485133278834775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1292398329656755519223183 1938597494485133278834775)
          ·
            refine ⟨2907896241727699918252163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1938597494485133278834775 2907896241727699918252163)
            ·
              refine ⟨4361844362591549877378245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2907896241727699918252163 4361844362591549877378245)
              ·
                refine ⟨817845817985915602008421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4361844362591549877378245 817845817985915602008421)
                ·
                  refine ⟨153346090872359175376579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 817845817985915602008421 153346090872359175376579)
                  ·
                    rfl

theorem cell22_1343882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 4, 4].length) (baseStart_1343882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1343882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1343882 prefixEnd_1343882 := by exact prefixLift 1343882
  have htrace : WordTrace (prefixWord ++ tailWord_1343882) baseStart_1343882 baseEnd_1343882 := by
    simpa [prefixWord, tailWord_1343882, baseEnd_1343882] using wordTrace_append hprefix tailTrace_1343882
  have hstable : (prefixWord ++ tailWord_1343882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343882).length < 2 ^ (prefixWord ++ tailWord_1343882).sum := by decide
  have hdescent : baseEnd_1343882 < baseStart_1343882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343908 : List Nat := [2, 3, 1, 2, 1, 1, 3, 1, 5, 3]
def baseStart_1343908 : Nat := 118140960795 + 1343908 * 2 ^ 59
def prefixEnd_1343908 : Nat := 4983230072969 + 3 ^ 40 * 1343908 * 2
def baseEnd_1343908 : Nat := 460047172948422124979657

theorem tailTrace_1343908 : CollatzResearch.WordTrace tailWord_1343908 prefixEnd_1343908 460047172948422124979657 := by
  unfold tailWord_1343908
  simp only [CollatzResearch.WordTrace]
  refine ⟨24508175807629156029196189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32677567743505541372261585 24508175807629156029196189)
  ·
    refine ⟨9190565927860933510948571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24508175807629156029196189 9190565927860933510948571)
    ·
      refine ⟨13785848891791400266422857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9190565927860933510948571 13785848891791400266422857)
      ·
        refine ⟨10339386668843550199817143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13785848891791400266422857 10339386668843550199817143)
        ·
          refine ⟨15509080003265325299725715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10339386668843550199817143 15509080003265325299725715)
          ·
            refine ⟨23263620004897987949588573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15509080003265325299725715 23263620004897987949588573)
            ·
              refine ⟨8723857501836745481095715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23263620004897987949588573 8723857501836745481095715)
              ·
                refine ⟨13085786252755118221643573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8723857501836745481095715 13085786252755118221643573)
                ·
                  refine ⟨1226792461195792333279085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13085786252755118221643573 1226792461195792333279085)
                  ·
                    refine ⟨460047172948422124979657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1226792461195792333279085 460047172948422124979657)
                    ·
                      rfl

theorem cell22_1343908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 5, 3].length) (baseStart_1343908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1343908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1343908 prefixEnd_1343908 := by exact prefixLift 1343908
  have htrace : WordTrace (prefixWord ++ tailWord_1343908) baseStart_1343908 baseEnd_1343908 := by
    simpa [prefixWord, tailWord_1343908, baseEnd_1343908] using wordTrace_append hprefix tailTrace_1343908
  have hstable : (prefixWord ++ tailWord_1343908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343908).length < 2 ^ (prefixWord ++ tailWord_1343908).sum := by decide
  have hdescent : baseEnd_1343908 < baseStart_1343908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343912 : List Nat := [2, 1, 6, 1, 1, 3, 1, 1, 2, 4]
def baseStart_1343912 : Nat := 118140960795 + 1343912 * 2 ^ 59
def prefixEnd_1343912 : Nat := 4983230072969 + 3 ^ 40 * 1343912 * 2
def baseEnd_1343912 : Nat := 460048542230167447879645

theorem tailTrace_1343912 : CollatzResearch.WordTrace tailWord_1343912 prefixEnd_1343912 460048542230167447879645 := by
  unfold tailWord_1343912
  simp only [CollatzResearch.WordTrace]
  refine ⟨24508248753621910370768995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32677665004829213827691993 24508248753621910370768995)
  ·
    refine ⟨36762373130432865556153493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24508248753621910370768995 36762373130432865556153493)
    ·
      refine ⟨1723236240489040572944695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 36762373130432865556153493 1723236240489040572944695)
      ·
        refine ⟨2584854360733560859417043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1723236240489040572944695 2584854360733560859417043)
        ·
          refine ⟨3877281541100341289125565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2584854360733560859417043 3877281541100341289125565)
          ·
            refine ⟨1453980577912627983422087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3877281541100341289125565 1453980577912627983422087)
            ·
              refine ⟨2180970866868941975133131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1453980577912627983422087 2180970866868941975133131)
              ·
                refine ⟨3271456300303412962699697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2180970866868941975133131 3271456300303412962699697)
                ·
                  refine ⟨2453592225227559722024773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3271456300303412962699697 2453592225227559722024773)
                  ·
                    refine ⟨460048542230167447879645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2453592225227559722024773 460048542230167447879645)
                    ·
                      rfl

theorem cell22_1343912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_1343912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1343912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1343912 prefixEnd_1343912 := by exact prefixLift 1343912
  have htrace : WordTrace (prefixWord ++ tailWord_1343912) baseStart_1343912 baseEnd_1343912 := by
    simpa [prefixWord, tailWord_1343912, baseEnd_1343912] using wordTrace_append hprefix tailTrace_1343912
  have hstable : (prefixWord ++ tailWord_1343912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343912).length < 2 ^ (prefixWord ++ tailWord_1343912).sum := by decide
  have hdescent : baseEnd_1343912 < baseStart_1343912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344006 : List Nat := [6, 2, 1, 1, 1, 1, 4, 1, 5]
def baseStart_1344006 : Nat := 118140960795 + 1344006 * 2 ^ 59
def prefixEnd_1344006 : Nat := 4983230072969 + 3 ^ 40 * 1344006 * 2
def baseEnd_1344006 : Nat := 153360240117060845343119

theorem tailTrace_1344006 : CollatzResearch.WordTrace tailWord_1344006 prefixEnd_1344006 153360240117060845343119 := by
  unfold tailWord_1344006
  simp only [CollatzResearch.WordTrace]
  refine ⟨1531872686528227337358121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 32679950645935516530306581 1531872686528227337358121)
  ·
    refine ⟨1148904514896170503018591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1531872686528227337358121 1148904514896170503018591)
    ·
      refine ⟨1723356772344255754527887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1148904514896170503018591 1723356772344255754527887)
      ·
        refine ⟨2585035158516383631791831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1723356772344255754527887 2585035158516383631791831)
        ·
          refine ⟨3877552737774575447687747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2585035158516383631791831 3877552737774575447687747)
          ·
            refine ⟨5816329106661863171531621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3877552737774575447687747 5816329106661863171531621)
            ·
              refine ⟨1090561707499099344662179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5816329106661863171531621 1090561707499099344662179)
              ·
                refine ⟨1635842561248649016993269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1090561707499099344662179 1635842561248649016993269)
                ·
                  refine ⟨153360240117060845343119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1635842561248649016993269 153360240117060845343119)
                  ·
                    rfl

theorem cell22_1344006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_1344006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1344006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1344006 prefixEnd_1344006 := by exact prefixLift 1344006
  have htrace : WordTrace (prefixWord ++ tailWord_1344006) baseStart_1344006 baseEnd_1344006 := by
    simpa [prefixWord, tailWord_1344006, baseEnd_1344006] using wordTrace_append hprefix tailTrace_1344006
  have hstable : (prefixWord ++ tailWord_1344006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344006).length < 2 ^ (prefixWord ++ tailWord_1344006).sum := by decide
  have hdescent : baseEnd_1344006 < baseStart_1344006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344028 : List Nat := [2, 2, 3, 1, 2, 2, 2, 8]
def baseStart_1344028 : Nat := 118140960795 + 1344028 * 2 ^ 59
def prefixEnd_1344028 : Nat := 4983230072969 + 3 ^ 40 * 1344028 * 2
def baseEnd_1344028 : Nat := 51120916822309090219921

theorem tailTrace_1344028 : CollatzResearch.WordTrace tailWord_1344028 prefixEnd_1344028 51120916822309090219921 := by
  unfold tailWord_1344028
  simp only [CollatzResearch.WordTrace]
  refine ⟨24510364187411786276380369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32680485583215715035173825 24510364187411786276380369)
  ·
    refine ⟨18382773140558839707285277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24510364187411786276380369 18382773140558839707285277)
    ·
      refine ⟨6893539927709564890231979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18382773140558839707285277 6893539927709564890231979)
      ·
        refine ⟨10340309891564347335347969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6893539927709564890231979 10340309891564347335347969)
        ·
          refine ⟨7755232418673260501510977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10340309891564347335347969 7755232418673260501510977)
          ·
            refine ⟨5816424314004945376133233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7755232418673260501510977 5816424314004945376133233)
            ·
              refine ⟨4362318235503709032099925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5816424314004945376133233 4362318235503709032099925)
              ·
                refine ⟨51120916822309090219921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4362318235503709032099925 51120916822309090219921)
                ·
                  rfl

theorem cell22_1344028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 8].length) (baseStart_1344028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1344028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1344028 prefixEnd_1344028 := by exact prefixLift 1344028
  have htrace : WordTrace (prefixWord ++ tailWord_1344028) baseStart_1344028 baseEnd_1344028 := by
    simpa [prefixWord, tailWord_1344028, baseEnd_1344028] using wordTrace_append hprefix tailTrace_1344028
  have hstable : (prefixWord ++ tailWord_1344028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344028).length < 2 ^ (prefixWord ++ tailWord_1344028).sum := by decide
  have hdescent : baseEnd_1344028 < baseStart_1344028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344058 : List Nat := [3, 1, 1, 1, 3, 3, 1, 1, 2, 6]
def baseStart_1344058 : Nat := 118140960795 + 1344058 * 2 ^ 59
def prefixEnd_1344058 : Nat := 4983230072969 + 3 ^ 40 * 1344058 * 2
def baseEnd_1344058 : Nat := 460098521013871733729197

theorem tailTrace_1344058 : CollatzResearch.WordTrace tailWord_1344058 prefixEnd_1344058 460098521013871733729197 := by
  unfold tailWord_1344058
  simp only [CollatzResearch.WordTrace]
  refine ⟨12255455641178721919088207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32681215043143258450901885 12255455641178721919088207)
  ·
    refine ⟨18383183461768082878632311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12255455641178721919088207 18383183461768082878632311)
    ·
      refine ⟨27574775192652124317948467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18383183461768082878632311 27574775192652124317948467)
      ·
        refine ⟨41362162788978186476922701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27574775192652124317948467 41362162788978186476922701)
        ·
          refine ⟨15510811045866819928846013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41362162788978186476922701 15510811045866819928846013)
          ·
            refine ⟨5816554142200057473317255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15510811045866819928846013 5816554142200057473317255)
            ·
              refine ⟨8724831213300086209975883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5816554142200057473317255 8724831213300086209975883)
              ·
                refine ⟨13087246819950129314963825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8724831213300086209975883 13087246819950129314963825)
                ·
                  refine ⟨9815435114962596986222869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13087246819950129314963825 9815435114962596986222869)
                  ·
                    refine ⟨460098521013871733729197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9815435114962596986222869 460098521013871733729197)
                    ·
                      rfl

theorem cell22_1344058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 2, 6].length) (baseStart_1344058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1344058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1344058 prefixEnd_1344058 := by exact prefixLift 1344058
  have htrace : WordTrace (prefixWord ++ tailWord_1344058) baseStart_1344058 baseEnd_1344058 := by
    simpa [prefixWord, tailWord_1344058, baseEnd_1344058] using wordTrace_append hprefix tailTrace_1344058
  have hstable : (prefixWord ++ tailWord_1344058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344058).length < 2 ^ (prefixWord ++ tailWord_1344058).sum := by decide
  have hdescent : baseEnd_1344058 < baseStart_1344058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344077 : List Nat := [1, 6, 1, 1, 2, 1, 1, 1, 5, 3]
def baseStart_1344077 : Nat := 118140960795 + 1344077 * 2 ^ 59
def prefixEnd_1344077 : Nat := 4983230072969 + 3 ^ 40 * 1344077 * 2
def baseEnd_1344077 : Nat := 460105025102162017504139

theorem tailTrace_1344077 : CollatzResearch.WordTrace tailWord_1344077 prefixEnd_1344077 460105025102162017504139 := by
  unfold tailWord_1344077
  simp only [CollatzResearch.WordTrace]
  refine ⟨49022515551646053921294485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32681677034430702614196323 49022515551646053921294485)
  ·
    refine ⟨2297930416483408777560679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 49022515551646053921294485 2297930416483408777560679)
    ·
      refine ⟨3446895624725113166341019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2297930416483408777560679 3446895624725113166341019)
      ·
        refine ⟨5170343437087669749511529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3446895624725113166341019 5170343437087669749511529)
        ·
          refine ⟨3877757577815752312133647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5170343437087669749511529 3877757577815752312133647)
          ·
            refine ⟨5816636366723628468200471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3877757577815752312133647 5816636366723628468200471)
            ·
              refine ⟨8724954550085442702300707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5816636366723628468200471 8724954550085442702300707)
              ·
                refine ⟨13087431825128164053451061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8724954550085442702300707 13087431825128164053451061)
                ·
                  refine ⟨1226946733605765380011037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13087431825128164053451061 1226946733605765380011037)
                  ·
                    refine ⟨460105025102162017504139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1226946733605765380011037 460105025102162017504139)
                    ·
                      rfl

theorem cell22_1344077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_1344077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1344077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1344077 prefixEnd_1344077 := by exact prefixLift 1344077
  have htrace : WordTrace (prefixWord ++ tailWord_1344077) baseStart_1344077 baseEnd_1344077 := by
    simpa [prefixWord, tailWord_1344077, baseEnd_1344077] using wordTrace_append hprefix tailTrace_1344077
  have hstable : (prefixWord ++ tailWord_1344077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344077).length < 2 ^ (prefixWord ++ tailWord_1344077).sum := by decide
  have hdescent : baseEnd_1344077 < baseStart_1344077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344240 : List Nat := [2, 1, 1, 1, 3, 1, 5, 1, 2, 5]
def baseStart_1344240 : Nat := 118140960795 + 1344240 * 2 ^ 59
def prefixEnd_1344240 : Nat := 4983230072969 + 3 ^ 40 * 1344240 * 2
def baseEnd_1344240 : Nat := 460160823333283925678639

theorem tailTrace_1344240 : CollatzResearch.WordTrace tailWord_1344240 prefixEnd_1344240 460160823333283925678639 := by
  unfold tailWord_1344240
  simp only [CollatzResearch.WordTrace]
  refine ⟨24514230325027766379739087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32685640433370355172985449 24514230325027766379739087)
  ·
    refine ⟨36771345487541649569608631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24514230325027766379739087 36771345487541649569608631)
    ·
      refine ⟨55157018231312474354412947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36771345487541649569608631 55157018231312474354412947)
      ·
        refine ⟨82735527346968711531619421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55157018231312474354412947 82735527346968711531619421)
        ·
          refine ⟨31025822755113266824357283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82735527346968711531619421 31025822755113266824357283)
          ·
            refine ⟨46538734132669900236535925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31025822755113266824357283 46538734132669900236535925)
            ·
              refine ⟨4363006324937803147175243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46538734132669900236535925 4363006324937803147175243)
              ·
                refine ⟨6544509487406704720762865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4363006324937803147175243 6544509487406704720762865)
                ·
                  refine ⟨4908382115555028540572149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6544509487406704720762865 4908382115555028540572149)
                  ·
                    refine ⟨460160823333283925678639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4908382115555028540572149 460160823333283925678639)
                    ·
                      rfl

theorem cell22_1344240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 2, 5].length) (baseStart_1344240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1344240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1344240 prefixEnd_1344240 := by exact prefixLift 1344240
  have htrace : WordTrace (prefixWord ++ tailWord_1344240) baseStart_1344240 baseEnd_1344240 := by
    simpa [prefixWord, tailWord_1344240, baseEnd_1344240] using wordTrace_append hprefix tailTrace_1344240
  have hstable : (prefixWord ++ tailWord_1344240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344240).length < 2 ^ (prefixWord ++ tailWord_1344240).sum := by decide
  have hdescent : baseEnd_1344240 < baseStart_1344240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344242 : List Nat := [3, 2, 1, 3, 1, 2, 2, 3, 5]
def baseStart_1344242 : Nat := 118140960795 + 1344242 * 2 ^ 59
def prefixEnd_1344242 : Nat := 4983230072969 + 3 ^ 40 * 1344242 * 2
def baseEnd_1344242 : Nat := 153387169324718862376211

theorem tailTrace_1344242 : CollatzResearch.WordTrace tailWord_1344242 prefixEnd_1344242 153387169324718862376211 := by
  unfold tailWord_1344242
  simp only [CollatzResearch.WordTrace]
  refine ⟨12257133399012071775262745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32685689064032191400700653 12257133399012071775262745)
  ·
    refine ⟨9192850049259053831447059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12257133399012071775262745 9192850049259053831447059)
    ·
      refine ⟨13789275073888580747170589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9192850049259053831447059 13789275073888580747170589)
      ·
        refine ⟨5170978152708217780188971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13789275073888580747170589 5170978152708217780188971)
        ·
          refine ⟨7756467229062326670283457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5170978152708217780188971 7756467229062326670283457)
          ·
            refine ⟨5817350421796745002712593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7756467229062326670283457 5817350421796745002712593)
            ·
              refine ⟨4363012816347558752034445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5817350421796745002712593 4363012816347558752034445)
              ·
                refine ⟨1636129806130334532012917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4363012816347558752034445 1636129806130334532012917)
                ·
                  refine ⟨153387169324718862376211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1636129806130334532012917 153387169324718862376211)
                  ·
                    rfl

theorem cell22_1344242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 3, 5].length) (baseStart_1344242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1344242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1344242 prefixEnd_1344242 := by exact prefixLift 1344242
  have htrace : WordTrace (prefixWord ++ tailWord_1344242) baseStart_1344242 baseEnd_1344242 := by
    simpa [prefixWord, tailWord_1344242, baseEnd_1344242] using wordTrace_append hprefix tailTrace_1344242
  have hstable : (prefixWord ++ tailWord_1344242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344242).length < 2 ^ (prefixWord ++ tailWord_1344242).sum := by decide
  have hdescent : baseEnd_1344242 < baseStart_1344242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344270 : List Nat := [4, 1, 1, 2, 1, 1, 1, 1, 10]
def baseStart_1344270 : Nat := 118140960795 + 1344270 * 2 ^ 59
def prefixEnd_1344270 : Nat := 4983230072969 + 3 ^ 40 * 1344270 * 2
def baseEnd_1344270 : Nat := 153390364315457949142849

theorem tailTrace_1344270 : CollatzResearch.WordTrace tailWord_1344270 prefixEnd_1344270 153390364315457949142849 := by
  unfold tailWord_1344270
  simp only [CollatzResearch.WordTrace]
  refine ⟨6128694354993355985383783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32686369893297898588713509 6128694354993355985383783)
  ·
    refine ⟨9193041532490033978075675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6128694354993355985383783 9193041532490033978075675)
    ·
      refine ⟨13789562298735050967113513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9193041532490033978075675 13789562298735050967113513)
      ·
        refine ⟨10342171724051288225335135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13789562298735050967113513 10342171724051288225335135)
        ·
          refine ⟨15513257586076932338002703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10342171724051288225335135 15513257586076932338002703)
          ·
            refine ⟨23269886379115398507004055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15513257586076932338002703 23269886379115398507004055)
            ·
              refine ⟨34904829568673097760506083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23269886379115398507004055 34904829568673097760506083)
              ·
                refine ⟨52357244353009646640759125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34904829568673097760506083 52357244353009646640759125)
                ·
                  refine ⟨153390364315457949142849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 52357244353009646640759125 153390364315457949142849)
                  ·
                    rfl

theorem cell22_1344270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 10].length) (baseStart_1344270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1344270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1344270 prefixEnd_1344270 := by exact prefixLift 1344270
  have htrace : WordTrace (prefixWord ++ tailWord_1344270) baseStart_1344270 baseEnd_1344270 := by
    simpa [prefixWord, tailWord_1344270, baseEnd_1344270] using wordTrace_append hprefix tailTrace_1344270
  have hstable : (prefixWord ++ tailWord_1344270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344270).length < 2 ^ (prefixWord ++ tailWord_1344270).sum := by decide
  have hdescent : baseEnd_1344270 < baseStart_1344270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344287 : List Nat := [1, 1, 2, 4, 2, 3, 2, 1, 6]
def baseStart_1344287 : Nat := 118140960795 + 1344287 * 2 ^ 59
def prefixEnd_1344287 : Nat := 4983230072969 + 3 ^ 40 * 1344287 * 2
def baseEnd_1344287 : Nat := 153392304131263823251165

theorem tailTrace_1344287 : CollatzResearch.WordTrace tailWord_1344287 prefixEnd_1344287 153392304131263823251165 := by
  unfold tailWord_1344287
  simp only [CollatzResearch.WordTrace]
  refine ⟨49030174880885259786439115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32686783253923506524292743 49030174880885259786439115)
  ·
    refine ⟨73545262321327889679658673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49030174880885259786439115 73545262321327889679658673)
    ·
      refine ⟨55158946740995917259744005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73545262321327889679658673 55158946740995917259744005)
      ·
        refine ⟨10342302513936734486202001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55158946740995917259744005 10342302513936734486202001)
        ·
          refine ⟨7756726885452550864651501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10342302513936734486202001 7756726885452550864651501)
          ·
            refine ⟨2908772582044706574244313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7756726885452550864651501 2908772582044706574244313)
            ·
              refine ⟨2181579436533529930683235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2908772582044706574244313 2181579436533529930683235)
              ·
                refine ⟨3272369154800294896024853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2181579436533529930683235 3272369154800294896024853)
                ·
                  refine ⟨153392304131263823251165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3272369154800294896024853 153392304131263823251165)
                  ·
                    rfl

theorem cell22_1344287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 1, 6].length) (baseStart_1344287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1344287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1344287 prefixEnd_1344287 := by exact prefixLift 1344287
  have htrace : WordTrace (prefixWord ++ tailWord_1344287) baseStart_1344287 baseEnd_1344287 := by
    simpa [prefixWord, tailWord_1344287, baseEnd_1344287] using wordTrace_append hprefix tailTrace_1344287
  have hstable : (prefixWord ++ tailWord_1344287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344287).length < 2 ^ (prefixWord ++ tailWord_1344287).sum := by decide
  have hdescent : baseEnd_1344287 < baseStart_1344287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344300 : List Nat := [2, 2, 1, 1, 1, 4, 1, 1, 3, 6]
def baseStart_1344300 : Nat := 118140960795 + 1344300 * 2 ^ 59
def prefixEnd_1344300 : Nat := 4983230072969 + 3 ^ 40 * 1344300 * 2
def baseEnd_1344300 : Nat := 460181362559463769178455

theorem tailTrace_1344300 : CollatzResearch.WordTrace tailWord_1344300 prefixEnd_1344300 460181362559463769178455 := by
  unfold tailWord_1344300
  simp only [CollatzResearch.WordTrace]
  refine ⟨24515324514919081503331177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32687099353225442004441569 24515324514919081503331177)
  ·
    refine ⟨18386493386189311127498383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24515324514919081503331177 18386493386189311127498383)
    ·
      refine ⟨27579740079283966691247575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18386493386189311127498383 27579740079283966691247575)
      ·
        refine ⟨41369610118925950036871363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27579740079283966691247575 41369610118925950036871363)
        ·
          refine ⟨62054415178388925055307045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41369610118925950036871363 62054415178388925055307045)
          ·
            refine ⟨11635202845947923447870071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62054415178388925055307045 11635202845947923447870071)
            ·
              refine ⟨17452804268921885171805107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11635202845947923447870071 17452804268921885171805107)
              ·
                refine ⟨26179206403382827757707661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17452804268921885171805107 26179206403382827757707661)
                ·
                  refine ⟨9817202401268560409140373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26179206403382827757707661 9817202401268560409140373)
                  ·
                    refine ⟨460181362559463769178455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9817202401268560409140373 460181362559463769178455)
                    ·
                      rfl

theorem cell22_1344300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 6].length) (baseStart_1344300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1344300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1344300 prefixEnd_1344300 := by exact prefixLift 1344300
  have htrace : WordTrace (prefixWord ++ tailWord_1344300) baseStart_1344300 baseEnd_1344300 := by
    simpa [prefixWord, tailWord_1344300, baseEnd_1344300] using wordTrace_append hprefix tailTrace_1344300
  have hstable : (prefixWord ++ tailWord_1344300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344300).length < 2 ^ (prefixWord ++ tailWord_1344300).sum := by decide
  have hdescent : baseEnd_1344300 < baseStart_1344300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344332 : List Nat := [2, 2, 1, 3, 3, 3, 8]
def baseStart_1344332 : Nat := 118140960795 + 1344332 * 2 ^ 59
def prefixEnd_1344332 : Nat := 4983230072969 + 3 ^ 40 * 1344332 * 2
def baseEnd_1344332 : Nat := 17044159881978753791791

theorem tailTrace_1344332 : CollatzResearch.WordTrace tailWord_1344332 prefixEnd_1344332 17044159881978753791791 := by
  unfold tailWord_1344332
  simp only [CollatzResearch.WordTrace]
  refine ⟨24515908082861116235913625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32687877443814821647884833 24515908082861116235913625)
  ·
    refine ⟨18386931062145837176935219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24515908082861116235913625 18386931062145837176935219)
    ·
      refine ⟨27580396593218755765402829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18386931062145837176935219 27580396593218755765402829)
      ·
        refine ⟨10342648722457033412026061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27580396593218755765402829 10342648722457033412026061)
        ·
          refine ⟨3878493270921387529509773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10342648722457033412026061 3878493270921387529509773)
          ·
            refine ⟨1454434976595520323566165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3878493270921387529509773 1454434976595520323566165)
            ·
              refine ⟨17044159881978753791791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1454434976595520323566165 17044159881978753791791)
              ·
                rfl

theorem cell22_1344332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 8].length) (baseStart_1344332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1344332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1344332 prefixEnd_1344332 := by exact prefixLift 1344332
  have htrace : WordTrace (prefixWord ++ tailWord_1344332) baseStart_1344332 baseEnd_1344332 := by
    simpa [prefixWord, tailWord_1344332, baseEnd_1344332] using wordTrace_append hprefix tailTrace_1344332
  have hstable : (prefixWord ++ tailWord_1344332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344332).length < 2 ^ (prefixWord ++ tailWord_1344332).sum := by decide
  have hdescent : baseEnd_1344332 < baseStart_1344332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344394 : List Nat := [3, 1, 2, 4, 1, 1, 1, 4, 5]
def baseStart_1344394 : Nat := 118140960795 + 1344394 * 2 ^ 59
def prefixEnd_1344394 : Nat := 4983230072969 + 3 ^ 40 * 1344394 * 2
def baseEnd_1344394 : Nat := 153404513560159619109389

theorem tailTrace_1344394 : CollatzResearch.WordTrace tailWord_1344394 prefixEnd_1344394 153404513560159619109389 := by
  unfold tailWord_1344394
  simp only [CollatzResearch.WordTrace]
  refine ⟨12258519372874404265146059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32689384994331744707056157 12258519372874404265146059)
  ·
    refine ⟨18387779059311606397719089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12258519372874404265146059 18387779059311606397719089)
    ·
      refine ⟨13790834294483704798289317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18387779059311606397719089 13790834294483704798289317)
      ·
        refine ⟨2585781430215694649679247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13790834294483704798289317 2585781430215694649679247)
        ·
          refine ⟨3878672145323541974518871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2585781430215694649679247 3878672145323541974518871)
          ·
            refine ⟨5818008217985312961778307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3878672145323541974518871 5818008217985312961778307)
            ·
              refine ⟨8727012326977969442667461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5818008217985312961778307 8727012326977969442667461)
              ·
                refine ⟨1636314811308369270500149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8727012326977969442667461 1636314811308369270500149)
                ·
                  refine ⟨153404513560159619109389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1636314811308369270500149 153404513560159619109389)
                  ·
                    rfl

theorem cell22_1344394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 4, 5].length) (baseStart_1344394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1344394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1344394 prefixEnd_1344394 := by exact prefixLift 1344394
  have htrace : WordTrace (prefixWord ++ tailWord_1344394) baseStart_1344394 baseEnd_1344394 := by
    simpa [prefixWord, tailWord_1344394, baseEnd_1344394] using wordTrace_append hprefix tailTrace_1344394
  have hstable : (prefixWord ++ tailWord_1344394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344394).length < 2 ^ (prefixWord ++ tailWord_1344394).sum := by decide
  have hdescent : baseEnd_1344394 < baseStart_1344394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344407 : List Nat := [1, 1, 3, 3, 1, 2, 1, 1, 5, 4]
def baseStart_1344407 : Nat := 118140960795 + 1344407 * 2 ^ 59
def prefixEnd_1344407 : Nat := 4983230072969 + 3 ^ 40 * 1344407 * 2
def baseEnd_1344407 : Nat := 460217990846151156753127

theorem tailTrace_1344407 : CollatzResearch.WordTrace tailWord_1344407 prefixEnd_1344407 460217990846151156753127 := by
  unfold tailWord_1344407
  simp only [CollatzResearch.WordTrace]
  refine ⟨49034551640450520280807475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32689701093633680187204983 49034551640450520280807475)
  ·
    refine ⟨73551827460675780421211213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49034551640450520280807475 73551827460675780421211213)
    ·
      refine ⟨27581935297753417657954205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73551827460675780421211213 27581935297753417657954205)
      ·
        refine ⟨10343225736657531621732827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27581935297753417657954205 10343225736657531621732827)
        ·
          refine ⟨15514838604986297432599241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10343225736657531621732827 15514838604986297432599241)
          ·
            refine ⟨11636128953739723074449431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15514838604986297432599241 11636128953739723074449431)
            ·
              refine ⟨17454193430609584611674147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11636128953739723074449431 17454193430609584611674147)
              ·
                refine ⟨26181290145914376917511221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17454193430609584611674147 26181290145914376917511221)
                ·
                  refine ⟨2454495951179472836016677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26181290145914376917511221 2454495951179472836016677)
                  ·
                    refine ⟨460217990846151156753127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2454495951179472836016677 460217990846151156753127)
                    ·
                      rfl

theorem cell22_1344407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 5, 4].length) (baseStart_1344407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1344407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1344407 prefixEnd_1344407 := by exact prefixLift 1344407
  have htrace : WordTrace (prefixWord ++ tailWord_1344407) baseStart_1344407 baseEnd_1344407 := by
    simpa [prefixWord, tailWord_1344407, baseEnd_1344407] using wordTrace_append hprefix tailTrace_1344407
  have hstable : (prefixWord ++ tailWord_1344407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344407).length < 2 ^ (prefixWord ++ tailWord_1344407).sum := by decide
  have hdescent : baseEnd_1344407 < baseStart_1344407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344439 : List Nat := [1, 1, 3, 1, 3, 1, 3, 5, 4]
def baseStart_1344439 : Nat := 118140960795 + 1344439 * 2 ^ 59
def prefixEnd_1344439 : Nat := 4983230072969 + 3 ^ 40 * 1344439 * 2
def baseEnd_1344439 : Nat := 153409648366704579984343

theorem tailTrace_1344439 : CollatzResearch.WordTrace tailWord_1344439 prefixEnd_1344439 153409648366704579984343 := by
  unfold tailWord_1344439
  simp only [CollatzResearch.WordTrace]
  refine ⟨49035718776334589745972371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32690479184223059830648247 49035718776334589745972371)
  ·
    refine ⟨73553578164501884618958557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49035718776334589745972371 73553578164501884618958557)
    ·
      refine ⟨27582591811688206732109459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73553578164501884618958557 27582591811688206732109459)
      ·
        refine ⟨41373887717532310098164189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27582591811688206732109459 41373887717532310098164189)
        ·
          refine ⟨15515207894074616286811571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41373887717532310098164189 15515207894074616286811571)
          ·
            refine ⟨23272811841111924430217357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15515207894074616286811571 23272811841111924430217357)
            ·
              refine ⟨8727304440416971661331509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23272811841111924430217357 8727304440416971661331509)
              ·
                refine ⟨818184791289091093249829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8727304440416971661331509 818184791289091093249829)
                ·
                  refine ⟨153409648366704579984343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 818184791289091093249829 153409648366704579984343)
                  ·
                    rfl

theorem cell22_1344439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 5, 4].length) (baseStart_1344439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1344439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1344439 prefixEnd_1344439 := by exact prefixLift 1344439
  have htrace : WordTrace (prefixWord ++ tailWord_1344439) baseStart_1344439 baseEnd_1344439 := by
    simpa [prefixWord, tailWord_1344439, baseEnd_1344439] using wordTrace_append hprefix tailTrace_1344439
  have hstable : (prefixWord ++ tailWord_1344439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344439).length < 2 ^ (prefixWord ++ tailWord_1344439).sum := by decide
  have hdescent : baseEnd_1344439 < baseStart_1344439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344441 : List Nat := [1, 2, 1, 4, 2, 2, 4, 1, 1, 4]
def baseStart_1344441 : Nat := 118140960795 + 1344441 * 2 ^ 59
def prefixEnd_1344441 : Nat := 4983230072969 + 3 ^ 40 * 1344441 * 2
def baseEnd_1344441 : Nat := 460229629740986401403023

theorem tailTrace_1344441 : CollatzResearch.WordTrace tailWord_1344441 prefixEnd_1344441 460229629740986401403023 := by
  unfold tailWord_1344441
  simp only [CollatzResearch.WordTrace]
  refine ⟨49035791722327344087545177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32690527814884896058363451 49035791722327344087545177)
  ·
    refine ⟨36776843791745508065658883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49035791722327344087545177 36776843791745508065658883)
    ·
      refine ⟨55165265687618262098488325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36776843791745508065658883 55165265687618262098488325)
      ·
        refine ⟨10343487316428424143466561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55165265687618262098488325 10343487316428424143466561)
        ·
          refine ⟨7757615487321318107599921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10343487316428424143466561 7757615487321318107599921)
          ·
            refine ⟨5818211615490988580699941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7757615487321318107599921 5818211615490988580699941)
            ·
              refine ⟨1090914677904560358881239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5818211615490988580699941 1090914677904560358881239)
              ·
                refine ⟨1636372016856840538321859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1090914677904560358881239 1636372016856840538321859)
                ·
                  refine ⟨2454558025285260807482789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1636372016856840538321859 2454558025285260807482789)
                  ·
                    refine ⟨460229629740986401403023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2454558025285260807482789 460229629740986401403023)
                    ·
                      rfl

theorem cell22_1344441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4, 1, 1, 4].length) (baseStart_1344441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1344441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1344441 prefixEnd_1344441 := by exact prefixLift 1344441
  have htrace : WordTrace (prefixWord ++ tailWord_1344441) baseStart_1344441 baseEnd_1344441 := by
    simpa [prefixWord, tailWord_1344441, baseEnd_1344441] using wordTrace_append hprefix tailTrace_1344441
  have hstable : (prefixWord ++ tailWord_1344441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344441).length < 2 ^ (prefixWord ++ tailWord_1344441).sum := by decide
  have hdescent : baseEnd_1344441 < baseStart_1344441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344610 : List Nat := [3, 3, 2, 2, 1, 1, 4, 1, 1, 4]
def baseStart_1344610 : Nat := 118140960795 + 1344610 * 2 ^ 59
def prefixEnd_1344610 : Nat := 4983230072969 + 3 ^ 40 * 1344610 * 2
def baseEnd_1344610 : Nat := 460287481894726293927505

theorem tailTrace_1344610 : CollatzResearch.WordTrace tailWord_1344610 prefixEnd_1344610 460287481894726293927505 := by
  unfold tailWord_1344610
  simp only [CollatzResearch.WordTrace]
  refine ⟨12260488914678771487611821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32694637105810057300298189 12260488914678771487611821)
  ·
    refine ⟨4597683343004539307854433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12260488914678771487611821 4597683343004539307854433)
    ·
      refine ⟨3448262507253404480890825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4597683343004539307854433 3448262507253404480890825)
      ·
        refine ⟨2586196880440053360668119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3448262507253404480890825 2586196880440053360668119)
        ·
          refine ⟨3879295320660080041002179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2586196880440053360668119 3879295320660080041002179)
          ·
            refine ⟨5818942980990120061503269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3879295320660080041002179 5818942980990120061503269)
            ·
              refine ⟨1091051808935647511531863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5818942980990120061503269 1091051808935647511531863)
              ·
                refine ⟨1636577713403471267297795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1091051808935647511531863 1636577713403471267297795)
                ·
                  refine ⟨2454866570105206900946693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1636577713403471267297795 2454866570105206900946693)
                  ·
                    refine ⟨460287481894726293927505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2454866570105206900946693 460287481894726293927505)
                    ·
                      rfl

theorem cell22_1344610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_1344610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1344610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1344610 prefixEnd_1344610 := by exact prefixLift 1344610
  have htrace : WordTrace (prefixWord ++ tailWord_1344610) baseStart_1344610 baseEnd_1344610 := by
    simpa [prefixWord, tailWord_1344610, baseEnd_1344610] using wordTrace_append hprefix tailTrace_1344610
  have hstable : (prefixWord ++ tailWord_1344610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344610).length < 2 ^ (prefixWord ++ tailWord_1344610).sum := by decide
  have hdescent : baseEnd_1344610 < baseStart_1344610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344709 : List Nat := [1, 3, 1, 1, 1, 1, 3, 3, 8]
def baseStart_1344709 : Nat := 118140960795 + 1344709 * 2 ^ 59
def prefixEnd_1344709 : Nat := 4983230072969 + 3 ^ 40 * 1344709 * 2
def baseEnd_1344709 : Nat := 153440457205974345234067

theorem tailTrace_1344709 : CollatzResearch.WordTrace tailWord_1344709 prefixEnd_1344709 153440457205974345234067 := by
  unfold tailWord_1344709
  simp only [CollatzResearch.WordTrace]
  refine ⟨49045566485356425858301181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32697044323570950572200787 49045566485356425858301181)
  ·
    refine ⟨18392087432008659696862943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49045566485356425858301181 18392087432008659696862943)
    ·
      refine ⟨27588131148012989545294415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18392087432008659696862943 27588131148012989545294415)
      ·
        refine ⟨41382196722019484317941623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27588131148012989545294415 41382196722019484317941623)
        ·
          refine ⟨62073295083029226476912435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41382196722019484317941623 62073295083029226476912435)
          ·
            refine ⟨93109942624543839715368653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62073295083029226476912435 93109942624543839715368653)
            ·
              refine ⟨34916228484203939893263245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93109942624543839715368653 34916228484203939893263245)
              ·
                refine ⟨13093585681576477459973717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34916228484203939893263245 13093585681576477459973717)
                ·
                  refine ⟨153440457205974345234067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13093585681576477459973717 153440457205974345234067)
                  ·
                    rfl

theorem cell22_1344709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 8].length) (baseStart_1344709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1344709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1344709 prefixEnd_1344709 := by exact prefixLift 1344709
  have htrace : WordTrace (prefixWord ++ tailWord_1344709) baseStart_1344709 baseEnd_1344709 := by
    simpa [prefixWord, tailWord_1344709, baseEnd_1344709] using wordTrace_append hprefix tailTrace_1344709
  have hstable : (prefixWord ++ tailWord_1344709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344709).length < 2 ^ (prefixWord ++ tailWord_1344709).sum := by decide
  have hdescent : baseEnd_1344709 < baseStart_1344709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344758 : List Nat := [5, 1, 1, 1, 1, 1, 1, 2, 6, 3]
def baseStart_1344758 : Nat := 118140960795 + 1344758 * 2 ^ 59
def prefixEnd_1344758 : Nat := 4983230072969 + 3 ^ 40 * 1344758 * 2
def baseEnd_1344758 : Nat := 460338145319303241227051

theorem tailTrace_1344758 : CollatzResearch.WordTrace tailWord_1344758 prefixEnd_1344758 460338145319303241227051 := by
  unfold tailWord_1344758
  simp only [CollatzResearch.WordTrace]
  refine ⟨3065459603886181701677183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32698235774785938151223285 3065459603886181701677183)
  ·
    refine ⟨4598189405829272552515775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3065459603886181701677183 4598189405829272552515775)
    ·
      refine ⟨6897284108743908828773663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4598189405829272552515775 6897284108743908828773663)
      ·
        refine ⟨10345926163115863243160495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6897284108743908828773663 10345926163115863243160495)
        ·
          refine ⟨15518889244673794864740743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10345926163115863243160495 15518889244673794864740743)
          ·
            refine ⟨23278333867010692297111115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15518889244673794864740743 23278333867010692297111115)
            ·
              refine ⟨34917500800516038445666673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23278333867010692297111115 34917500800516038445666673)
              ·
                refine ⟨26188125600387028834250005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34917500800516038445666673 26188125600387028834250005)
                ·
                  refine ⟨1227568387518141976605469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 26188125600387028834250005 1227568387518141976605469)
                  ·
                    refine ⟨460338145319303241227051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1227568387518141976605469 460338145319303241227051)
                    ·
                      rfl

theorem cell22_1344758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_1344758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1344758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1344758 prefixEnd_1344758 := by exact prefixLift 1344758
  have htrace : WordTrace (prefixWord ++ tailWord_1344758) baseStart_1344758 baseEnd_1344758 := by
    simpa [prefixWord, tailWord_1344758, baseEnd_1344758] using wordTrace_append hprefix tailTrace_1344758
  have hstable : (prefixWord ++ tailWord_1344758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344758).length < 2 ^ (prefixWord ++ tailWord_1344758).sum := by decide
  have hdescent : baseEnd_1344758 < baseStart_1344758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344803 : List Nat := [1, 1, 1, 4, 2, 3, 1, 3, 3, 3]
def baseStart_1344803 : Nat := 118140960795 + 1344803 * 2 ^ 59
def prefixEnd_1344803 : Nat := 4983230072969 + 3 ^ 40 * 1344803 * 2
def baseEnd_1344803 : Nat := 460353549738938123851913

theorem tailTrace_1344803 : CollatzResearch.WordTrace tailWord_1344803 prefixEnd_1344803 460353549738938123851913 := by
  unfold tailWord_1344803
  simp only [CollatzResearch.WordTrace]
  refine ⟨49048994947015879912223063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32699329964677253274815375 49048994947015879912223063)
  ·
    refine ⟨73573492420523819868334595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49048994947015879912223063 73573492420523819868334595)
    ·
      refine ⟨110360238630785729802501893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73573492420523819868334595 110360238630785729802501893)
      ·
        refine ⟨20692544743272324337969105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110360238630785729802501893 20692544743272324337969105)
        ·
          refine ⟨15519408557454243253476829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20692544743272324337969105 15519408557454243253476829)
          ·
            refine ⟨5819778209045341220053811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15519408557454243253476829 5819778209045341220053811)
            ·
              refine ⟨8729667313568011830080717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5819778209045341220053811 8729667313568011830080717)
              ·
                refine ⟨3273625242588004436280269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8729667313568011830080717 3273625242588004436280269)
                ·
                  refine ⟨1227609465970501663605101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3273625242588004436280269 1227609465970501663605101)
                  ·
                    refine ⟨460353549738938123851913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1227609465970501663605101 460353549738938123851913)
                    ·
                      rfl

theorem cell22_1344803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 3, 3, 3].length) (baseStart_1344803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1344803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1344803 prefixEnd_1344803 := by exact prefixLift 1344803
  have htrace : WordTrace (prefixWord ++ tailWord_1344803) baseStart_1344803 baseEnd_1344803 := by
    simpa [prefixWord, tailWord_1344803, baseEnd_1344803] using wordTrace_append hprefix tailTrace_1344803
  have hstable : (prefixWord ++ tailWord_1344803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344803).length < 2 ^ (prefixWord ++ tailWord_1344803).sum := by decide
  have hdescent : baseEnd_1344803 < baseStart_1344803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344820 : List Nat := [2, 5, 1, 1, 1, 1, 1, 4, 3, 3]
def baseStart_1344820 : Nat := 118140960795 + 1344820 * 2 ^ 59
def prefixEnd_1344820 : Nat := 4983230072969 + 3 ^ 40 * 1344820 * 2
def baseEnd_1344820 : Nat := 460359369186355746176861

theorem tailTrace_1344820 : CollatzResearch.WordTrace tailWord_1344820 prefixEnd_1344820 460359369186355746176861 := by
  unfold tailWord_1344820
  simp only [CollatzResearch.WordTrace]
  refine ⟨24524807493977145907795957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32699743325302861210394609 24524807493977145907795957)
  ·
    refine ⟨2299200702560357428855871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24524807493977145907795957 2299200702560357428855871)
    ·
      refine ⟨3448801053840536143283807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2299200702560357428855871 3448801053840536143283807)
      ·
        refine ⟨5173201580760804214925711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3448801053840536143283807 5173201580760804214925711)
        ·
          refine ⟨7759802371141206322388567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5173201580760804214925711 7759802371141206322388567)
          ·
            refine ⟨11639703556711809483582851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7759802371141206322388567 11639703556711809483582851)
            ·
              refine ⟨17459555335067714225374277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11639703556711809483582851 17459555335067714225374277)
              ·
                refine ⟨3273666625325196417257677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17459555335067714225374277 3273666625325196417257677)
                ·
                  refine ⟨1227624984496948656471629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3273666625325196417257677 1227624984496948656471629)
                  ·
                    refine ⟨460359369186355746176861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1227624984496948656471629 460359369186355746176861)
                    ·
                      rfl

theorem cell22_1344820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_1344820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1344820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1344820 prefixEnd_1344820 := by exact prefixLift 1344820
  have htrace : WordTrace (prefixWord ++ tailWord_1344820) baseStart_1344820 baseEnd_1344820 := by
    simpa [prefixWord, tailWord_1344820, baseEnd_1344820] using wordTrace_append hprefix tailTrace_1344820
  have hstable : (prefixWord ++ tailWord_1344820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344820).length < 2 ^ (prefixWord ++ tailWord_1344820).sum := by decide
  have hdescent : baseEnd_1344820 < baseStart_1344820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344833 : List Nat := [1, 2, 5, 2, 1, 1, 1, 2, 7]
def baseStart_1344833 : Nat := 118140960795 + 1344833 * 2 ^ 59
def prefixEnd_1344833 : Nat := 4983230072969 + 3 ^ 40 * 1344833 * 2
def baseEnd_1344833 : Nat := 153454606450676015200607

theorem tailTrace_1344833 : CollatzResearch.WordTrace tailWord_1344833 prefixEnd_1344833 153454606450676015200607 := by
  unfold tailWord_1344833
  simp only [CollatzResearch.WordTrace]
  refine ⟨49050089136907195035815153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32700059424604796690543435 49050089136907195035815153)
  ·
    refine ⟨36787566852680396276861365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49050089136907195035815153 36787566852680396276861365)
    ·
      refine ⟨3448834392438787150955753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36787566852680396276861365 3448834392438787150955753)
      ·
        refine ⟨2586625794329090363216815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3448834392438787150955753 2586625794329090363216815)
        ·
          refine ⟨3879938691493635544825223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2586625794329090363216815 3879938691493635544825223)
          ·
            refine ⟨5819908037240453317237835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3879938691493635544825223 5819908037240453317237835)
            ·
              refine ⟨8729862055860679975856753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5819908037240453317237835 8729862055860679975856753)
              ·
                refine ⟨6547396541895509981892565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8729862055860679975856753 6547396541895509981892565)
                ·
                  refine ⟨153454606450676015200607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6547396541895509981892565 153454606450676015200607)
                  ·
                    rfl

theorem cell22_1344833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 7].length) (baseStart_1344833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1344833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1344833 prefixEnd_1344833 := by exact prefixLift 1344833
  have htrace : WordTrace (prefixWord ++ tailWord_1344833) baseStart_1344833 baseEnd_1344833 := by
    simpa [prefixWord, tailWord_1344833, baseEnd_1344833] using wordTrace_append hprefix tailTrace_1344833
  have hstable : (prefixWord ++ tailWord_1344833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344833).length < 2 ^ (prefixWord ++ tailWord_1344833).sum := by decide
  have hdescent : baseEnd_1344833 < baseStart_1344833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344893 : List Nat := [1, 4, 1, 1, 2, 2, 3, 2, 1, 5]
def baseStart_1344893 : Nat := 118140960795 + 1344893 * 2 ^ 59
def prefixEnd_1344893 : Nat := 4983230072969 + 3 ^ 40 * 1344893 * 2
def baseEnd_1344893 : Nat := 460384358578207889101637

theorem tailTrace_1344893 : CollatzResearch.WordTrace tailWord_1344893 prefixEnd_1344893 460384358578207889101637 := by
  unfold tailWord_1344893
  simp only [CollatzResearch.WordTrace]
  refine ⟨49052277516689825282999333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32701518344459883521999555 49052277516689825282999333)
  ·
    refine ⟨9197302034379342240562375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49052277516689825282999333 9197302034379342240562375)
    ·
      refine ⟨13795953051569013360843563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9197302034379342240562375 13795953051569013360843563)
      ·
        refine ⟨20693929577353520041265345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13795953051569013360843563 20693929577353520041265345)
        ·
          refine ⟨15520447183015140030949009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20693929577353520041265345 15520447183015140030949009)
          ·
            refine ⟨11640335387261355023211757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15520447183015140030949009 11640335387261355023211757)
            ·
              refine ⟨4365125770223008133704409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11640335387261355023211757 4365125770223008133704409)
              ·
                refine ⟨3273844327667256100278307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4365125770223008133704409 3273844327667256100278307)
                ·
                  refine ⟨4910766491500884150417461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3273844327667256100278307 4910766491500884150417461)
                  ·
                    refine ⟨460384358578207889101637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4910766491500884150417461 460384358578207889101637)
                    ·
                      rfl

theorem cell22_1344893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_1344893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1344893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1344893 prefixEnd_1344893 := by exact prefixLift 1344893
  have htrace : WordTrace (prefixWord ++ tailWord_1344893) baseStart_1344893 baseEnd_1344893 := by
    simpa [prefixWord, tailWord_1344893, baseEnd_1344893] using wordTrace_append hprefix tailTrace_1344893
  have hstable : (prefixWord ++ tailWord_1344893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344893).length < 2 ^ (prefixWord ++ tailWord_1344893).sum := by decide
  have hdescent : baseEnd_1344893 < baseStart_1344893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344906 : List Nat := [3, 1, 2, 16]
def baseStart_1344906 : Nat := 118140960795 + 1344906 * 2 ^ 59
def prefixEnd_1344906 : Nat := 4983230072969 + 3 ^ 40 * 1344906 * 2
def baseEnd_1344906 : Nat := 631534717069794497293

theorem tailTrace_1344906 : CollatzResearch.WordTrace tailWord_1344906 prefixEnd_1344906 631534717069794497293 := by
  unfold tailWord_1344906
  simp only [CollatzResearch.WordTrace]
  refine ⟨12263187916410682125805643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32701834443761819002148381 12263187916410682125805643)
  ·
    refine ⟨18394781874616023188708465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12263187916410682125805643 18394781874616023188708465)
    ·
      refine ⟨13796086405962017391531349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18394781874616023188708465 13796086405962017391531349)
      ·
        refine ⟨631534717069794497293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 16 13796086405962017391531349 631534717069794497293)
        ·
          rfl

theorem cell22_1344906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 16].length) (baseStart_1344906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1344906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1344906 prefixEnd_1344906 := by exact prefixLift 1344906
  have htrace : WordTrace (prefixWord ++ tailWord_1344906) baseStart_1344906 baseEnd_1344906 := by
    simpa [prefixWord, tailWord_1344906, baseEnd_1344906] using wordTrace_append hprefix tailTrace_1344906
  have hstable : (prefixWord ++ tailWord_1344906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344906).length < 2 ^ (prefixWord ++ tailWord_1344906).sum := by decide
  have hdescent : baseEnd_1344906 < baseStart_1344906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344908 : List Nat := [2, 2, 1, 2, 1, 3, 1, 4, 2, 4]
def baseStart_1344908 : Nat := 118140960795 + 1344908 * 2 ^ 59
def prefixEnd_1344908 : Nat := 4983230072969 + 3 ^ 40 * 1344908 * 2
def baseEnd_1344908 : Nat := 460389493384752849976591

theorem tailTrace_1344908 : CollatzResearch.WordTrace tailWord_1344908 prefixEnd_1344908 460389493384752849976591 := by
  unfold tailWord_1344908
  simp only [CollatzResearch.WordTrace]
  refine ⟨24526412305817741422397689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32701883074423655229863585 24526412305817741422397689)
  ·
    refine ⟨18394809229363306066798267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24526412305817741422397689 18394809229363306066798267)
    ·
      refine ⟨27592213844044959100197401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18394809229363306066798267 27592213844044959100197401)
      ·
        refine ⟨20694160383033719325148051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27592213844044959100197401 20694160383033719325148051)
        ·
          refine ⟨31041240574550578987722077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20694160383033719325148051 31041240574550578987722077)
          ·
            refine ⟨11640465215456467120395779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31041240574550578987722077 11640465215456467120395779)
            ·
              refine ⟨17460697823184700680593669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11640465215456467120395779 17460697823184700680593669)
              ·
                refine ⟨3273880841847131377611313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17460697823184700680593669 3273880841847131377611313)
                ·
                  refine ⟨2455410631385348533208485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3273880841847131377611313 2455410631385348533208485)
                  ·
                    refine ⟨460389493384752849976591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2455410631385348533208485 460389493384752849976591)
                    ·
                      rfl

theorem cell22_1344908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4, 2, 4].length) (baseStart_1344908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1344908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1344908 prefixEnd_1344908 := by exact prefixLift 1344908
  have htrace : WordTrace (prefixWord ++ tailWord_1344908) baseStart_1344908 baseEnd_1344908 := by
    simpa [prefixWord, tailWord_1344908, baseEnd_1344908] using wordTrace_append hprefix tailTrace_1344908
  have hstable : (prefixWord ++ tailWord_1344908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344908).length < 2 ^ (prefixWord ++ tailWord_1344908).sum := by decide
  have hdescent : baseEnd_1344908 < baseStart_1344908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344968 : List Nat := [2, 1, 3, 1, 3, 1, 3, 1, 7]
def baseStart_1344968 : Nat := 118140960795 + 1344968 * 2 ^ 59
def prefixEnd_1344968 : Nat := 4983230072969 + 3 ^ 40 * 1344968 * 2
def baseEnd_1344968 : Nat := 153470010870310897825469

theorem tailTrace_1344968 : CollatzResearch.WordTrace tailWord_1344968 prefixEnd_1344968 153470010870310897825469 := by
  unfold tailWord_1344968
  simp only [CollatzResearch.WordTrace]
  refine ⟨24527506495709056545989779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32703341994278742061319705 24527506495709056545989779)
  ·
    refine ⟨36791259743563584818984669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24527506495709056545989779 36791259743563584818984669)
    ·
      refine ⟨13796722403836344307119251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36791259743563584818984669 13796722403836344307119251)
      ·
        refine ⟨20695083605754516460678877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13796722403836344307119251 20695083605754516460678877)
        ·
          refine ⟨7760656352157943672754579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20695083605754516460678877 7760656352157943672754579)
          ·
            refine ⟨11640984528236915509131869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7760656352157943672754579 11640984528236915509131869)
            ·
              refine ⟨4365369198088843315924451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11640984528236915509131869 4365369198088843315924451)
              ·
                refine ⟨6548053797133264973886677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4365369198088843315924451 6548053797133264973886677)
                ·
                  refine ⟨153470010870310897825469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6548053797133264973886677 153470010870310897825469)
                  ·
                    rfl

theorem cell22_1344968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 7].length) (baseStart_1344968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1344968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1344968 prefixEnd_1344968 := by exact prefixLift 1344968
  have htrace : WordTrace (prefixWord ++ tailWord_1344968) baseStart_1344968 baseEnd_1344968 := by
    simpa [prefixWord, tailWord_1344968, baseEnd_1344968] using wordTrace_append hprefix tailTrace_1344968
  have hstable : (prefixWord ++ tailWord_1344968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344968).length < 2 ^ (prefixWord ++ tailWord_1344968).sum := by decide
  have hdescent : baseEnd_1344968 < baseStart_1344968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344972 : List Nat := [2, 2, 1, 4, 2, 2, 2, 1, 3, 3]
def baseStart_1344972 : Nat := 118140960795 + 1344972 * 2 ^ 59
def prefixEnd_1344972 : Nat := 4983230072969 + 3 ^ 40 * 1344972 * 2
def baseEnd_1344972 : Nat := 460411401892678016376395

theorem tailTrace_1344972 : CollatzResearch.WordTrace tailWord_1344972 prefixEnd_1344972 460411401892678016376395 := by
  unfold tailWord_1344972
  simp only [CollatzResearch.WordTrace]
  refine ⟨24527579441701810887562585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32703439255602414516750113 24527579441701810887562585)
  ·
    refine ⟨18395684581276358165671939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24527579441701810887562585 18395684581276358165671939)
    ·
      refine ⟨27593526871914537248507909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18395684581276358165671939 27593526871914537248507909)
      ·
        refine ⟨5173786288483975734095233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27593526871914537248507909 5173786288483975734095233)
        ·
          refine ⟨3880339716362981800571425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5173786288483975734095233 3880339716362981800571425)
          ·
            refine ⟨2910254787272236350428569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3880339716362981800571425 2910254787272236350428569)
            ·
              refine ⟨2182691090454177262821427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2910254787272236350428569 2182691090454177262821427)
              ·
                refine ⟨3274036635681265894232141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2182691090454177262821427 3274036635681265894232141)
                ·
                  refine ⟨1227763738380474710337053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3274036635681265894232141 1227763738380474710337053)
                  ·
                    refine ⟨460411401892678016376395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1227763738380474710337053 460411401892678016376395)
                    ·
                      rfl

theorem cell22_1344972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 1, 3, 3].length) (baseStart_1344972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1344972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1344972 prefixEnd_1344972 := by exact prefixLift 1344972
  have htrace : WordTrace (prefixWord ++ tailWord_1344972) baseStart_1344972 baseEnd_1344972 := by
    simpa [prefixWord, tailWord_1344972, baseEnd_1344972] using wordTrace_append hprefix tailTrace_1344972
  have hstable : (prefixWord ++ tailWord_1344972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344972).length < 2 ^ (prefixWord ++ tailWord_1344972).sum := by decide
  have hdescent : baseEnd_1344972 < baseStart_1344972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345103 : List Nat := [1, 1, 2, 1, 1, 2, 3, 2, 9]
def baseStart_1345103 : Nat := 118140960795 + 1345103 * 2 ^ 59
def prefixEnd_1345103 : Nat := 4983230072969 + 3 ^ 40 * 1345103 * 2
def baseEnd_1345103 : Nat := 153485415289945780450331

theorem tailTrace_1345103 : CollatzResearch.WordTrace tailWord_1345103 prefixEnd_1345103 153485415289945780450331 := by
  unfold tailWord_1345103
  simp only [CollatzResearch.WordTrace]
  refine ⟨49059936845929031148143963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32706624563952687432095975 49059936845929031148143963)
  ·
    refine ⟨73589905268893546722215945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49059936845929031148143963 73589905268893546722215945)
    ·
      refine ⟨55192428951670160041661959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73589905268893546722215945 55192428951670160041661959)
      ·
        refine ⟨82788643427505240062492939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55192428951670160041661959 82788643427505240062492939)
        ·
          refine ⟨124182965141257860093739409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82788643427505240062492939 124182965141257860093739409)
          ·
            refine ⟨93137223855943395070304557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124182965141257860093739409 93137223855943395070304557)
            ·
              refine ⟨34926458945978773151364209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93137223855943395070304557 34926458945978773151364209)
              ·
                refine ⟨26194844209484079863523157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34926458945978773151364209 26194844209484079863523157)
                ·
                  refine ⟨153485415289945780450331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 26194844209484079863523157 153485415289945780450331)
                  ·
                    rfl

theorem cell22_1345103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 9].length) (baseStart_1345103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1345103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1345103 prefixEnd_1345103 := by exact prefixLift 1345103
  have htrace : WordTrace (prefixWord ++ tailWord_1345103) baseStart_1345103 baseEnd_1345103 := by
    simpa [prefixWord, tailWord_1345103, baseEnd_1345103] using wordTrace_append hprefix tailTrace_1345103
  have hstable : (prefixWord ++ tailWord_1345103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345103).length < 2 ^ (prefixWord ++ tailWord_1345103).sum := by decide
  have hdescent : baseEnd_1345103 < baseStart_1345103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345124 : List Nat := [2, 3, 1, 1, 2, 3, 1, 5, 1, 3]
def baseStart_1345124 : Nat := 118140960795 + 1345124 * 2 ^ 59
def prefixEnd_1345124 : Nat := 4983230072969 + 3 ^ 40 * 1345124 * 2
def baseEnd_1345124 : Nat := 460463434599000286575929

theorem tailTrace_1345124 : CollatzResearch.WordTrace tailWord_1345124 prefixEnd_1345124 460463434599000286575929 := by
  unfold tailWord_1345124
  simp only [CollatzResearch.WordTrace]
  refine ⟨24530351389426475867329213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32707135185901967823105617 24530351389426475867329213)
  ·
    refine ⟨9198881771034928450248455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24530351389426475867329213 9198881771034928450248455)
    ·
      refine ⟨13798322656552392675372683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9198881771034928450248455 13798322656552392675372683)
      ·
        refine ⟨20697483984828589013059025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13798322656552392675372683 20697483984828589013059025)
        ·
          refine ⟨15523112988621441759794269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20697483984828589013059025 15523112988621441759794269)
          ·
            refine ⟨5821167370733040659922851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15523112988621441759794269 5821167370733040659922851)
            ·
              refine ⟨8731751056099560989884277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5821167370733040659922851 8731751056099560989884277)
              ·
                refine ⟨818601661509333842801651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8731751056099560989884277 818601661509333842801651)
                ·
                  refine ⟨1227902492264000764202477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 818601661509333842801651 1227902492264000764202477)
                  ·
                    refine ⟨460463434599000286575929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1227902492264000764202477 460463434599000286575929)
                    ·
                      rfl

theorem cell22_1345124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 5, 1, 3].length) (baseStart_1345124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1345124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1345124 prefixEnd_1345124 := by exact prefixLift 1345124
  have htrace : WordTrace (prefixWord ++ tailWord_1345124) baseStart_1345124 baseEnd_1345124 := by
    simpa [prefixWord, tailWord_1345124, baseEnd_1345124] using wordTrace_append hprefix tailTrace_1345124
  have hstable : (prefixWord ++ tailWord_1345124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345124).length < 2 ^ (prefixWord ++ tailWord_1345124).sum := by decide
  have hdescent : baseEnd_1345124 < baseStart_1345124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345141 : List Nat := [1, 3, 4, 2, 1, 1, 2, 4, 1, 3]
def baseStart_1345141 : Nat := 118140960795 + 1345141 * 2 ^ 59
def prefixEnd_1345141 : Nat := 4983230072969 + 3 ^ 40 * 1345141 * 2
def baseEnd_1345141 : Nat := 460469254046417908900877

theorem tailTrace_1345141 : CollatzResearch.WordTrace tailWord_1345141 prefixEnd_1345141 460469254046417908900877 := by
  unfold tailWord_1345141
  simp only [CollatzResearch.WordTrace]
  refine ⟨49061322819791363638027277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32707548546527575758684851 49061322819791363638027277)
  ·
    refine ⟨18397996057421761364260229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49061322819791363638027277 18397996057421761364260229)
    ·
      refine ⟨3449624260766580255798793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18397996057421761364260229 3449624260766580255798793)
      ·
        refine ⟨2587218195574935191849095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3449624260766580255798793 2587218195574935191849095)
        ·
          refine ⟨3880827293362402787773643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2587218195574935191849095 3880827293362402787773643)
          ·
            refine ⟨5821240940043604181660465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3880827293362402787773643 5821240940043604181660465)
            ·
              refine ⟨4365930705032703136245349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5821240940043604181660465 4365930705032703136245349)
              ·
                refine ⟨818612007193631838046003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4365930705032703136245349 818612007193631838046003)
                ·
                  refine ⟨1227918010790447757069005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 818612007193631838046003 1227918010790447757069005)
                  ·
                    refine ⟨460469254046417908900877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1227918010790447757069005 460469254046417908900877)
                    ·
                      rfl

theorem cell22_1345141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_1345141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1345141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1345141 prefixEnd_1345141 := by exact prefixLift 1345141
  have htrace : WordTrace (prefixWord ++ tailWord_1345141) baseStart_1345141 baseEnd_1345141 := by
    simpa [prefixWord, tailWord_1345141, baseEnd_1345141] using wordTrace_append hprefix tailTrace_1345141
  have hstable : (prefixWord ++ tailWord_1345141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345141).length < 2 ^ (prefixWord ++ tailWord_1345141).sum := by decide
  have hdescent : baseEnd_1345141 < baseStart_1345141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345192 : List Nat := [2, 1, 7, 1, 1, 1, 3, 2, 1, 3]
def baseStart_1345192 : Nat := 118140960795 + 1345192 * 2 ^ 59
def prefixEnd_1345192 : Nat := 4983230072969 + 3 ^ 40 * 1345192 * 2
def baseEnd_1345192 : Nat := 460486712388670775875721

theorem tailTrace_1345192 : CollatzResearch.WordTrace tailWord_1345192 prefixEnd_1345192 460486712388670775875721 := by
  unfold tailWord_1345192
  simp only [CollatzResearch.WordTrace]
  refine ⟨24531591471303299674066915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32708788628404399565422553 24531591471303299674066915)
  ·
    refine ⟨36797387206954949511100373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24531591471303299674066915 36797387206954949511100373)
    ·
      refine ⟨862438762663006629166415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 36797387206954949511100373 862438762663006629166415)
      ·
        refine ⟨1293658143994509943749623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 862438762663006629166415 1293658143994509943749623)
        ·
          refine ⟨1940487215991764915624435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1293658143994509943749623 1940487215991764915624435)
          ·
            refine ⟨2910730823987647373436653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1940487215991764915624435 2910730823987647373436653)
            ·
              refine ⟨1091524058995367765038745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2910730823987647373436653 1091524058995367765038745)
              ·
                refine ⟨818643044246525823779059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1091524058995367765038745 818643044246525823779059)
                ·
                  refine ⟨1227964566369788735668589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 818643044246525823779059 1227964566369788735668589)
                  ·
                    refine ⟨460486712388670775875721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1227964566369788735668589 460486712388670775875721)
                    ·
                      rfl

theorem cell22_1345192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_1345192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1345192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1345192 prefixEnd_1345192 := by exact prefixLift 1345192
  have htrace : WordTrace (prefixWord ++ tailWord_1345192) baseStart_1345192 baseEnd_1345192 := by
    simpa [prefixWord, tailWord_1345192, baseEnd_1345192] using wordTrace_append hprefix tailTrace_1345192
  have hstable : (prefixWord ++ tailWord_1345192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345192).length < 2 ^ (prefixWord ++ tailWord_1345192).sum := by decide
  have hdescent : baseEnd_1345192 < baseStart_1345192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345199 : List Nat := [1, 1, 2, 1, 2, 4, 5, 2, 4]
def baseStart_1345199 : Nat := 118140960795 + 1345199 * 2 ^ 59
def prefixEnd_1345199 : Nat := 4983230072969 + 3 ^ 40 * 1345199 * 2
def baseEnd_1345199 : Nat := 153496369543908363650233

theorem tailTrace_1345199 : CollatzResearch.WordTrace tailWord_1345199 prefixEnd_1345199 153496369543908363650233 := by
  unfold tailWord_1345199
  simp only [CollatzResearch.WordTrace]
  refine ⟨49063438253581239543638651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32708958835720826362425767 49063438253581239543638651)
  ·
    refine ⟨73595157380371859315457977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49063438253581239543638651 73595157380371859315457977)
    ·
      refine ⟨55196368035278894486593483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73595157380371859315457977 55196368035278894486593483)
      ·
        refine ⟨82794552052918341729890225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55196368035278894486593483 82794552052918341729890225)
        ·
          refine ⟨62095914039688756297417669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82794552052918341729890225 62095914039688756297417669)
          ·
            refine ⟨11642983882441641805765813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62095914039688756297417669 11642983882441641805765813)
            ·
              refine ⟨1091529738978903919290545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11642983882441641805765813 1091529738978903919290545)
              ·
                refine ⟨818647304234177939467909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1091529738978903919290545 818647304234177939467909)
                ·
                  refine ⟨153496369543908363650233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 818647304234177939467909 153496369543908363650233)
                  ·
                    rfl

theorem cell22_1345199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5, 2, 4].length) (baseStart_1345199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1345199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1345199 prefixEnd_1345199 := by exact prefixLift 1345199
  have htrace : WordTrace (prefixWord ++ tailWord_1345199) baseStart_1345199 baseEnd_1345199 := by
    simpa [prefixWord, tailWord_1345199, baseEnd_1345199] using wordTrace_append hprefix tailTrace_1345199
  have hstable : (prefixWord ++ tailWord_1345199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345199).length < 2 ^ (prefixWord ++ tailWord_1345199).sum := by decide
  have hdescent : baseEnd_1345199 < baseStart_1345199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345210 : List Nat := [3, 1, 1, 1, 2, 4, 1, 9]
def baseStart_1345210 : Nat := 118140960795 + 1345210 * 2 ^ 59
def prefixEnd_1345210 : Nat := 4983230072969 + 3 ^ 40 * 1345210 * 2
def baseEnd_1345210 : Nat := 51165874906280525436185

theorem tailTrace_1345210 : CollatzResearch.WordTrace tailWord_1345210 prefixEnd_1345210 51165874906280525436185 := by
  unfold tailWord_1345210
  simp only [CollatzResearch.WordTrace]
  refine ⟨12265959864135347105572271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32709226304360925614859389 12265959864135347105572271)
  ·
    refine ⟨18398939796203020658358407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12265959864135347105572271 18398939796203020658358407)
    ·
      refine ⟨27598409694304530987537611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18398939796203020658358407 27598409694304530987537611)
      ·
        refine ⟨41397614541456796481306417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27598409694304530987537611 41397614541456796481306417)
        ·
          refine ⟨31048210906092597360979813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41397614541456796481306417 31048210906092597360979813)
          ·
            refine ⟨5821539544892362005183715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31048210906092597360979813 5821539544892362005183715)
            ·
              refine ⟨8732309317338543007775573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5821539544892362005183715 8732309317338543007775573)
              ·
                refine ⟨51165874906280525436185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8732309317338543007775573 51165874906280525436185)
                ·
                  rfl

theorem cell22_1345210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 9].length) (baseStart_1345210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1345210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1345210 prefixEnd_1345210 := by exact prefixLift 1345210
  have htrace : WordTrace (prefixWord ++ tailWord_1345210) baseStart_1345210 baseEnd_1345210 := by
    simpa [prefixWord, tailWord_1345210, baseEnd_1345210] using wordTrace_append hprefix tailTrace_1345210
  have hstable : (prefixWord ++ tailWord_1345210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345210).length < 2 ^ (prefixWord ++ tailWord_1345210).sum := by decide
  have hdescent : baseEnd_1345210 < baseStart_1345210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345218 : List Nat := [3, 5, 1, 2, 1, 1, 1, 1, 3, 4]
def baseStart_1345218 : Nat := 118140960795 + 1345218 * 2 ^ 59
def prefixEnd_1345218 : Nat := 4983230072969 + 3 ^ 40 * 1345218 * 2
def baseEnd_1345218 : Nat := 460495612720015374725641

theorem tailTrace_1345218 : CollatzResearch.WordTrace tailWord_1345218 prefixEnd_1345218 460495612720015374725641 := by
  unfold tailWord_1345218
  simp only [CollatzResearch.WordTrace]
  refine ⟨12266032810128101447145077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32709420827008270525720205 12266032810128101447145077)
  ·
    refine ⟨1149940575949509510669851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12266032810128101447145077 1149940575949509510669851)
    ·
      refine ⟨1724910863924264266004777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1149940575949509510669851 1724910863924264266004777)
      ·
        refine ⟨1293683147943198199503583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1724910863924264266004777 1293683147943198199503583)
        ·
          refine ⟨1940524721914797299255375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1293683147943198199503583 1940524721914797299255375)
          ·
            refine ⟨2910787082872195948883063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1940524721914797299255375 2910787082872195948883063)
            ·
              refine ⟨4366180624308293923324595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2910787082872195948883063 4366180624308293923324595)
              ·
                refine ⟨6549270936462440884986893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4366180624308293923324595 6549270936462440884986893)
                ·
                  refine ⟨2455976601173415331870085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6549270936462440884986893 2455976601173415331870085)
                  ·
                    refine ⟨460495612720015374725641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2455976601173415331870085 460495612720015374725641)
                    ·
                      rfl

theorem cell22_1345218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_1345218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1345218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1345218 prefixEnd_1345218 := by exact prefixLift 1345218
  have htrace : WordTrace (prefixWord ++ tailWord_1345218) baseStart_1345218 baseEnd_1345218 := by
    simpa [prefixWord, tailWord_1345218, baseEnd_1345218] using wordTrace_append hprefix tailTrace_1345218
  have hstable : (prefixWord ++ tailWord_1345218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345218).length < 2 ^ (prefixWord ++ tailWord_1345218).sum := by decide
  have hdescent : baseEnd_1345218 < baseStart_1345218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345244 : List Nat := [2, 2, 5, 1, 3, 9]
def baseStart_1345244 : Nat := 118140960795 + 1345244 * 2 ^ 59
def prefixEnd_1345244 : Nat := 4983230072969 + 3 ^ 40 * 1345244 * 2
def baseEnd_1345244 : Nat := 5685240901868641649081

theorem tailTrace_1345244 : CollatzResearch.WordTrace tailWord_1345244 prefixEnd_1345244 5685240901868641649081 := by
  unfold tailWord_1345244
  simp only [CollatzResearch.WordTrace]
  refine ⟨24532539769209106114513393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32710053025612141486017857 24532539769209106114513393)
  ·
    refine ⟨18399404826906829585885045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24532539769209106114513393 18399404826906829585885045)
    ·
      refine ⟨1724944202522515273676723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18399404826906829585885045 1724944202522515273676723)
      ·
        refine ⟨2587416303783772910515085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1724944202522515273676723 2587416303783772910515085)
        ·
          refine ⟨970281113918914841443157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2587416303783772910515085 970281113918914841443157)
          ·
            refine ⟨5685240901868641649081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 970281113918914841443157 5685240901868641649081)
            ·
              rfl

theorem cell22_1345244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 9].length) (baseStart_1345244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1345244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1345244 prefixEnd_1345244 := by exact prefixLift 1345244
  have htrace : WordTrace (prefixWord ++ tailWord_1345244) baseStart_1345244 baseEnd_1345244 := by
    simpa [prefixWord, tailWord_1345244, baseEnd_1345244] using wordTrace_append hprefix tailTrace_1345244
  have hstable : (prefixWord ++ tailWord_1345244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345244).length < 2 ^ (prefixWord ++ tailWord_1345244).sum := by decide
  have hdescent : baseEnd_1345244 < baseStart_1345244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345286 : List Nat := [6, 2, 2, 1, 2, 1, 2, 1, 1, 4]
def baseStart_1345286 : Nat := 118140960795 + 1345286 * 2 ^ 59
def prefixEnd_1345286 : Nat := 4983230072969 + 3 ^ 40 * 1345286 * 2
def baseEnd_1345286 : Nat := 460518890509685864025433

theorem tailTrace_1345286 : CollatzResearch.WordTrace tailWord_1345286 prefixEnd_1345286 460518890509685864025433 := by
  unfold tailWord_1345286
  simp only [CollatzResearch.WordTrace]
  refine ⟨1533331606383314168814241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 32711074269510702268037141 1533331606383314168814241)
  ·
    refine ⟨1149998704787485626610681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1533331606383314168814241 1149998704787485626610681)
    ·
      refine ⟨862499028590614219958011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1149998704787485626610681 862499028590614219958011)
      ·
        refine ⟨1293748542885921329937017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 862499028590614219958011 1293748542885921329937017)
        ·
          refine ⟨970311407164440997452763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1293748542885921329937017 970311407164440997452763)
          ·
            refine ⟨1455467110746661496179145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 970311407164440997452763 1455467110746661496179145)
            ·
              refine ⟨1091600333059996122134359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1455467110746661496179145 1091600333059996122134359)
              ·
                refine ⟨1637400499589994183201539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1091600333059996122134359 1637400499589994183201539)
                ·
                  refine ⟨2456100749384991274802309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1637400499589994183201539 2456100749384991274802309)
                  ·
                    refine ⟨460518890509685864025433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2456100749384991274802309 460518890509685864025433)
                    ·
                      rfl

theorem cell22_1345286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_1345286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1345286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1345286 prefixEnd_1345286 := by exact prefixLift 1345286
  have htrace : WordTrace (prefixWord ++ tailWord_1345286) baseStart_1345286 baseEnd_1345286 := by
    simpa [prefixWord, tailWord_1345286, baseEnd_1345286] using wordTrace_append hprefix tailTrace_1345286
  have hstable : (prefixWord ++ tailWord_1345286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345286).length < 2 ^ (prefixWord ++ tailWord_1345286).sum := by decide
  have hdescent : baseEnd_1345286 < baseStart_1345286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345310 : List Nat := [4, 3, 2, 2, 1, 1, 2, 1, 3, 3]
def baseStart_1345310 : Nat := 118140960795 + 1345310 * 2 ^ 59
def prefixEnd_1345310 : Nat := 4983230072969 + 3 ^ 40 * 1345310 * 2
def baseEnd_1345310 : Nat := 460527106200157801425359

theorem tailTrace_1345310 : CollatzResearch.WordTrace tailWord_1345310 prefixEnd_1345310 460527106200157801425359 := by
  unfold tailWord_1345310
  simp only [CollatzResearch.WordTrace]
  refine ⟨6133435844522388187616173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32711657837452737000619589 6133435844522388187616173)
  ·
    refine ⟨2300038441695895570356065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6133435844522388187616173 2300038441695895570356065)
    ·
      refine ⟨1725028831271921677767049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2300038441695895570356065 1725028831271921677767049)
      ·
        refine ⟨1293771623453941258325287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1725028831271921677767049 1293771623453941258325287)
        ·
          refine ⟨1940657435180911887487931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1293771623453941258325287 1940657435180911887487931)
          ·
            refine ⟨2910986152771367831231897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1940657435180911887487931 2910986152771367831231897)
            ·
              refine ⟨2183239614578525873423923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2910986152771367831231897 2183239614578525873423923)
              ·
                refine ⟨3274859421867788810135885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2183239614578525873423923 3274859421867788810135885)
                ·
                  refine ⟨1228072283200420803800957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3274859421867788810135885 1228072283200420803800957)
                  ·
                    refine ⟨460527106200157801425359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1228072283200420803800957 460527106200157801425359)
                    ·
                      rfl

theorem cell22_1345310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_1345310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1345310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1345310 prefixEnd_1345310 := by exact prefixLift 1345310
  have htrace : WordTrace (prefixWord ++ tailWord_1345310) baseStart_1345310 baseEnd_1345310 := by
    simpa [prefixWord, tailWord_1345310, baseEnd_1345310] using wordTrace_append hprefix tailTrace_1345310
  have hstable : (prefixWord ++ tailWord_1345310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345310).length < 2 ^ (prefixWord ++ tailWord_1345310).sum := by decide
  have hdescent : baseEnd_1345310 < baseStart_1345310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345317 : List Nat := [1, 3, 1, 2, 3, 2, 1, 3, 6]
def baseStart_1345317 : Nat := 118140960795 + 1345317 * 2 ^ 59
def prefixEnd_1345317 : Nat := 4983230072969 + 3 ^ 40 * 1345317 * 2
def baseEnd_1345317 : Nat := 153509834147737372166779

theorem tailTrace_1345317 : CollatzResearch.WordTrace tailWord_1345317 prefixEnd_1345317 153509834147737372166779 := by
  unfold tailWord_1345317
  simp only [CollatzResearch.WordTrace]
  refine ⟨49067742067153745696434205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32711828044769163797622803 49067742067153745696434205)
  ·
    refine ⟨18400403275182654636162827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49067742067153745696434205 18400403275182654636162827)
    ·
      refine ⟨27600604912773981954244241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18400403275182654636162827 27600604912773981954244241)
      ·
        refine ⟨20700453684580486465683181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27600604912773981954244241 20700453684580486465683181)
        ·
          refine ⟨7762670131717682424631193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20700453684580486465683181 7762670131717682424631193)
          ·
            refine ⟨5822002598788261818473395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7762670131717682424631193 5822002598788261818473395)
            ·
              refine ⟨8733003898182392727710093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5822002598788261818473395 8733003898182392727710093)
              ·
                refine ⟨3274876461818397272891285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8733003898182392727710093 3274876461818397272891285)
                ·
                  refine ⟨153509834147737372166779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3274876461818397272891285 153509834147737372166779)
                  ·
                    rfl

theorem cell22_1345317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 3, 6].length) (baseStart_1345317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1345317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1345317 prefixEnd_1345317 := by exact prefixLift 1345317
  have htrace : WordTrace (prefixWord ++ tailWord_1345317) baseStart_1345317 baseEnd_1345317 := by
    simpa [prefixWord, tailWord_1345317, baseEnd_1345317] using wordTrace_append hprefix tailTrace_1345317
  have hstable : (prefixWord ++ tailWord_1345317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345317).length < 2 ^ (prefixWord ++ tailWord_1345317).sum := by decide
  have hdescent : baseEnd_1345317 < baseStart_1345317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345347 : List Nat := [1, 1, 1, 3, 1, 5, 2, 1, 1, 6]
def baseStart_1345347 : Nat := 118140960795 + 1345347 * 2 ^ 59
def prefixEnd_1345347 : Nat := 4983230072969 + 3 ^ 40 * 1345347 * 2
def baseEnd_1345347 : Nat := 460539772056302038250245

theorem tailTrace_1345347 : CollatzResearch.WordTrace tailWord_1345347 prefixEnd_1345347 460539772056302038250245 := by
  unfold tailWord_1345347
  simp only [CollatzResearch.WordTrace]
  refine ⟨49068836257045060820026295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32712557504696707213350863 49068836257045060820026295)
  ·
    refine ⟨73603254385567591230039443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49068836257045060820026295 73603254385567591230039443)
    ·
      refine ⟨110404881578351386845059165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73603254385567591230039443 110404881578351386845059165)
      ·
        refine ⟨41401830591881770066897187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110404881578351386845059165 41401830591881770066897187)
        ·
          refine ⟨62102745887822655100345781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41401830591881770066897187 62102745887822655100345781)
          ·
            refine ⟨5822132426983373915657417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62102745887822655100345781 5822132426983373915657417)
            ·
              refine ⟨4366599320237530436743063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5822132426983373915657417 4366599320237530436743063)
              ·
                refine ⟨6549898980356295655114595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4366599320237530436743063 6549898980356295655114595)
                ·
                  refine ⟨9824848470534443482671893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6549898980356295655114595 9824848470534443482671893)
                  ·
                    refine ⟨460539772056302038250245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9824848470534443482671893 460539772056302038250245)
                    ·
                      rfl

theorem cell22_1345347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 6].length) (baseStart_1345347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1345347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1345347 prefixEnd_1345347 := by exact prefixLift 1345347
  have htrace : WordTrace (prefixWord ++ tailWord_1345347) baseStart_1345347 baseEnd_1345347 := by
    simpa [prefixWord, tailWord_1345347, baseEnd_1345347] using wordTrace_append hprefix tailTrace_1345347
  have hstable : (prefixWord ++ tailWord_1345347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345347).length < 2 ^ (prefixWord ++ tailWord_1345347).sum := by decide
  have hdescent : baseEnd_1345347 < baseStart_1345347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345362 : List Nat := [3, 2, 2, 1, 1, 3, 10]
def baseStart_1345362 : Nat := 118140960795 + 1345362 * 2 ^ 59
def prefixEnd_1345362 : Nat := 4983230072969 + 3 ^ 40 * 1345362 * 2
def baseEnd_1345362 : Nat := 17057218772698037004637

theorem tailTrace_1345362 : CollatzResearch.WordTrace tailWord_1345362 prefixEnd_1345362 17057218772698037004637 := by
  unfold tailWord_1345362
  simp only [CollatzResearch.WordTrace]
  refine ⟨12267345837997679595455585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32712922234660478921214893 12267345837997679595455585)
  ·
    refine ⟨9200509378498259696591689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12267345837997679595455585 9200509378498259696591689)
    ·
      refine ⟨6900382033873694772443767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9200509378498259696591689 6900382033873694772443767)
      ·
        refine ⟨10350573050810542158665651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6900382033873694772443767 10350573050810542158665651)
        ·
          refine ⟨15525859576215813237998477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10350573050810542158665651 15525859576215813237998477)
          ·
            refine ⟨5822197341080929964249429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15525859576215813237998477 5822197341080929964249429)
            ·
              refine ⟨17057218772698037004637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5822197341080929964249429 17057218772698037004637)
              ·
                rfl

theorem cell22_1345362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 10].length) (baseStart_1345362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1345362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1345362 prefixEnd_1345362 := by exact prefixLift 1345362
  have htrace : WordTrace (prefixWord ++ tailWord_1345362) baseStart_1345362 baseEnd_1345362 := by
    simpa [prefixWord, tailWord_1345362, baseEnd_1345362] using wordTrace_append hprefix tailTrace_1345362
  have hstable : (prefixWord ++ tailWord_1345362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345362).length < 2 ^ (prefixWord ++ tailWord_1345362).sum := by decide
  have hdescent : baseEnd_1345362 < baseStart_1345362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345364 : List Nat := [2, 4, 1, 1, 3, 1, 1, 1, 4, 4]
def baseStart_1345364 : Nat := 118140960795 + 1345364 * 2 ^ 59
def prefixEnd_1345364 : Nat := 4983230072969 + 3 ^ 40 * 1345364 * 2
def baseEnd_1345364 : Nat := 460545591503719660575193

theorem tailTrace_1345364 : CollatzResearch.WordTrace tailWord_1345364 prefixEnd_1345364 460545591503719660575193 := by
  unfold tailWord_1345364
  simp only [CollatzResearch.WordTrace]
  refine ⟨24534728148991736361697573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32712970865322315148930097 24534728148991736361697573)
  ·
    refine ⟨4600261527935950567818295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24534728148991736361697573 4600261527935950567818295)
    ·
      refine ⟨6900392291903925851727443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4600261527935950567818295 6900392291903925851727443)
      ·
        refine ⟨10350588437855888777591165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6900392291903925851727443 10350588437855888777591165)
        ·
          refine ⟨3881470664195958291596687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10350588437855888777591165 3881470664195958291596687)
          ·
            refine ⟨5822205996293937437395031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3881470664195958291596687 5822205996293937437395031)
            ·
              refine ⟨8733308994440906156092547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5822205996293937437395031 8733308994440906156092547)
              ·
                refine ⟨13099963491661359234138821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8733308994440906156092547 13099963491661359234138821)
                ·
                  refine ⟨2456243154686504856401029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13099963491661359234138821 2456243154686504856401029)
                  ·
                    refine ⟨460545591503719660575193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2456243154686504856401029 460545591503719660575193)
                    ·
                      rfl

theorem cell22_1345364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_1345364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1345364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1345364 prefixEnd_1345364 := by exact prefixLift 1345364
  have htrace : WordTrace (prefixWord ++ tailWord_1345364) baseStart_1345364 baseEnd_1345364 := by
    simpa [prefixWord, tailWord_1345364, baseEnd_1345364] using wordTrace_append hprefix tailTrace_1345364
  have hstable : (prefixWord ++ tailWord_1345364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345364).length < 2 ^ (prefixWord ++ tailWord_1345364).sum := by decide
  have hdescent : baseEnd_1345364 < baseStart_1345364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345379 : List Nat := [1, 1, 1, 5, 4, 1, 2, 7]
def baseStart_1345379 : Nat := 118140960795 + 1345379 * 2 ^ 59
def prefixEnd_1345379 : Nat := 4983230072969 + 3 ^ 40 * 1345379 * 2
def baseEnd_1345379 : Nat := 51172302923362735716683

theorem tailTrace_1345379 : CollatzResearch.WordTrace tailWord_1345379 prefixEnd_1345379 51172302923362735716683 := by
  unfold tailWord_1345379
  simp only [CollatzResearch.WordTrace]
  refine ⟨49070003392929130285191191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32713335595286086856794127 49070003392929130285191191)
  ·
    refine ⟨73605005089393695427786787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49070003392929130285191191 73605005089393695427786787)
    ·
      refine ⟨110407507634090543141680181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73605005089393695427786787 110407507634090543141680181)
      ·
        refine ⟨10350703840695988419532517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 110407507634090543141680181 10350703840695988419532517)
        ·
          refine ⟨1940756970130497828662347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10350703840695988419532517 1940756970130497828662347)
          ·
            refine ⟨2911135455195746742993521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1940756970130497828662347 2911135455195746742993521)
            ·
              refine ⟨2183351591396810057245141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2911135455195746742993521 2183351591396810057245141)
              ·
                refine ⟨51172302923362735716683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2183351591396810057245141 51172302923362735716683)
                ·
                  rfl

theorem cell22_1345379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 7].length) (baseStart_1345379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1345379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1345379 prefixEnd_1345379 := by exact prefixLift 1345379
  have htrace : WordTrace (prefixWord ++ tailWord_1345379) baseStart_1345379 baseEnd_1345379 := by
    simpa [prefixWord, tailWord_1345379, baseEnd_1345379] using wordTrace_append hprefix tailTrace_1345379
  have hstable : (prefixWord ++ tailWord_1345379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345379).length < 2 ^ (prefixWord ++ tailWord_1345379).sum := by decide
  have hdescent : baseEnd_1345379 < baseStart_1345379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345394 : List Nat := [3, 2, 1, 2, 1, 1, 1, 3, 5, 3]
def baseStart_1345394 : Nat := 118140960795 + 1345394 * 2 ^ 59
def prefixEnd_1345394 : Nat := 4983230072969 + 3 ^ 40 * 1345394 * 2
def baseEnd_1345394 : Nat := 460555861116809582325101

theorem tailTrace_1345394 : CollatzResearch.WordTrace tailWord_1345394 prefixEnd_1345394 460555861116809582325101 := by
  unfold tailWord_1345394
  simp only [CollatzResearch.WordTrace]
  refine ⟨12267637621968696961746809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32713700325249858564658157 12267637621968696961746809)
  ·
    refine ⟨9200728216476522721310107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12267637621968696961746809 9200728216476522721310107)
    ·
      refine ⟨13801092324714784081965161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9200728216476522721310107 13801092324714784081965161)
      ·
        refine ⟨10350819243536088061473871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13801092324714784081965161 10350819243536088061473871)
        ·
          refine ⟨15526228865304132092210807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10350819243536088061473871 15526228865304132092210807)
          ·
            refine ⟨23289343297956198138316211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15526228865304132092210807 23289343297956198138316211)
            ·
              refine ⟨34934014946934297207474317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23289343297956198138316211 34934014946934297207474317)
              ·
                refine ⟨13100255605100361452802869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34934014946934297207474317 13100255605100361452802869)
                ·
                  refine ⟨1228148962978158886200269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13100255605100361452802869 1228148962978158886200269)
                  ·
                    refine ⟨460555861116809582325101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1228148962978158886200269 460555861116809582325101)
                    ·
                      rfl

theorem cell22_1345394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 5, 3].length) (baseStart_1345394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1345394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1345394 prefixEnd_1345394 := by exact prefixLift 1345394
  have htrace : WordTrace (prefixWord ++ tailWord_1345394) baseStart_1345394 baseEnd_1345394 := by
    simpa [prefixWord, tailWord_1345394, baseEnd_1345394] using wordTrace_append hprefix tailTrace_1345394
  have hstable : (prefixWord ++ tailWord_1345394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345394).length < 2 ^ (prefixWord ++ tailWord_1345394).sum := by decide
  have hdescent : baseEnd_1345394 < baseStart_1345394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345398 : List Nat := [5, 1, 1, 3, 2, 1, 2, 1, 2, 4]
def baseStart_1345398 : Nat := 118140960795 + 1345398 * 2 ^ 59
def prefixEnd_1345398 : Nat := 4983230072969 + 3 ^ 40 * 1345398 * 2
def baseEnd_1345398 : Nat := 460557230398554905225089

theorem tailTrace_1345398 : CollatzResearch.WordTrace tailWord_1345398 prefixEnd_1345398 460557230398554905225089 := by
  unfold tailWord_1345398
  simp only [CollatzResearch.WordTrace]
  refine ⟨3066918523741268533133303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32713797586573531020088565 3066918523741268533133303)
  ·
    refine ⟨4600377785611902799699955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3066918523741268533133303 4600377785611902799699955)
    ·
      refine ⟨6900566678417854199549933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4600377785611902799699955 6900566678417854199549933)
      ·
        refine ⟨2587712504406695324831225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6900566678417854199549933 2587712504406695324831225)
        ·
          refine ⟨1940784378305021493623419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2587712504406695324831225 1940784378305021493623419)
          ·
            refine ⟨2911176567457532240435129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1940784378305021493623419 2911176567457532240435129)
            ·
              refine ⟨2183382425593149180326347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2911176567457532240435129 2183382425593149180326347)
              ·
                refine ⟨3275073638389723770489521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2183382425593149180326347 3275073638389723770489521)
                ·
                  refine ⟨2456305228792292827867141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3275073638389723770489521 2456305228792292827867141)
                  ·
                    refine ⟨460557230398554905225089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2456305228792292827867141 460557230398554905225089)
                    ·
                      rfl

theorem cell22_1345398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_1345398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1345398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1345398 prefixEnd_1345398 := by exact prefixLift 1345398
  have htrace : WordTrace (prefixWord ++ tailWord_1345398) baseStart_1345398 baseEnd_1345398 := by
    simpa [prefixWord, tailWord_1345398, baseEnd_1345398] using wordTrace_append hprefix tailTrace_1345398
  have hstable : (prefixWord ++ tailWord_1345398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345398).length < 2 ^ (prefixWord ++ tailWord_1345398).sum := by decide
  have hdescent : baseEnd_1345398 < baseStart_1345398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345430 : List Nat := [5, 3, 1, 1, 2, 2, 1, 7]
def baseStart_1345430 : Nat := 118140960795 + 1345430 * 2 ^ 59
def prefixEnd_1345430 : Nat := 4983230072969 + 3 ^ 40 * 1345430 * 2
def baseEnd_1345430 : Nat := 51174242739168609824999

theorem tailTrace_1345430 : CollatzResearch.WordTrace tailWord_1345430 prefixEnd_1345430 51174242739168609824999 := by
  unfold tailWord_1345430
  simp only [CollatzResearch.WordTrace]
  refine ⟨3066991469734022874706109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32714575677162910663531829 3066991469734022874706109)
  ·
    refine ⟨1150121801150258578014791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3066991469734022874706109 1150121801150258578014791)
    ·
      refine ⟨1725182701725387867022187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1150121801150258578014791 1725182701725387867022187)
      ·
        refine ⟨2587774052588081800533281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1725182701725387867022187 2587774052588081800533281)
        ·
          refine ⟨1940830539441061350399961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2587774052588081800533281 1940830539441061350399961)
          ·
            refine ⟨1455622904580796012799971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1940830539441061350399961 1455622904580796012799971)
            ·
              refine ⟨2183434356871194019199957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1455622904580796012799971 2183434356871194019199957)
              ·
                refine ⟨51174242739168609824999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2183434356871194019199957 51174242739168609824999)
                ·
                  rfl

theorem cell22_1345430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 7].length) (baseStart_1345430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1345430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1345430 prefixEnd_1345430 := by exact prefixLift 1345430
  have htrace : WordTrace (prefixWord ++ tailWord_1345430) baseStart_1345430 baseEnd_1345430 := by
    simpa [prefixWord, tailWord_1345430, baseEnd_1345430] using wordTrace_append hprefix tailTrace_1345430
  have hstable : (prefixWord ++ tailWord_1345430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345430).length < 2 ^ (prefixWord ++ tailWord_1345430).sum := by decide
  have hdescent : baseEnd_1345430 < baseStart_1345430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345486 : List Nat := [4, 1, 1, 1, 2, 2, 1, 6, 4]
def baseStart_1345486 : Nat := 118140960795 + 1345486 * 2 ^ 59
def prefixEnd_1345486 : Nat := 4983230072969 + 3 ^ 40 * 1345486 * 2
def baseEnd_1345486 : Nat := 153529118198984003008273

theorem tailTrace_1345486 : CollatzResearch.WordTrace tailWord_1345486 prefixEnd_1345486 153529118198984003008273 := by
  unfold tailWord_1345486
  simp only [CollatzResearch.WordTrace]
  refine ⟨6134238250442685944917039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32715937335694325039557541 6134238250442685944917039)
  ·
    refine ⟨9201357375664028917375559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6134238250442685944917039 9201357375664028917375559)
    ·
      refine ⟨13802036063496043376063339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9201357375664028917375559 13802036063496043376063339)
      ·
        refine ⟨20703054095244065064095009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13802036063496043376063339 20703054095244065064095009)
        ·
          refine ⟨15527290571433048798071257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20703054095244065064095009 15527290571433048798071257)
          ·
            refine ⟨11645467928574786598553443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15527290571433048798071257 11645467928574786598553443)
            ·
              refine ⟨17468201892862179897830165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11645467928574786598553443 17468201892862179897830165)
              ·
                refine ⟨818821963727914682710789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17468201892862179897830165 818821963727914682710789)
                ·
                  refine ⟨153529118198984003008273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 818821963727914682710789 153529118198984003008273)
                  ·
                    rfl

theorem cell22_1345486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 6, 4].length) (baseStart_1345486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1345486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1345486 prefixEnd_1345486 := by exact prefixLift 1345486
  have htrace : WordTrace (prefixWord ++ tailWord_1345486) baseStart_1345486 baseEnd_1345486 := by
    simpa [prefixWord, tailWord_1345486, baseEnd_1345486] using wordTrace_append hprefix tailTrace_1345486
  have hstable : (prefixWord ++ tailWord_1345486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345486).length < 2 ^ (prefixWord ++ tailWord_1345486).sum := by decide
  have hdescent : baseEnd_1345486 < baseStart_1345486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345514 : List Nat := [3, 1, 3, 1, 2, 1, 3, 8]
def baseStart_1345514 : Nat := 118140960795 + 1345514 * 2 ^ 59
def prefixEnd_1345514 : Nat := 4983230072969 + 3 ^ 40 * 1345514 * 2
def baseEnd_1345514 : Nat := 51177437729907696591637

theorem tailTrace_1345514 : CollatzResearch.WordTrace tailWord_1345514 prefixEnd_1345514 51177437729907696591637 := by
  unfold tailWord_1345514
  simp only [CollatzResearch.WordTrace]
  refine ⟨12268731811860012085338899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32716618164960032227570397 12268731811860012085338899)
  ·
    refine ⟨18403097717790018128008349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12268731811860012085338899 18403097717790018128008349)
    ·
      refine ⟨6901161644171256798003131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18403097717790018128008349 6901161644171256798003131)
      ·
        refine ⟨10351742466256885197004697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6901161644171256798003131 10351742466256885197004697)
        ·
          refine ⟨7763806849692663897753523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10351742466256885197004697 7763806849692663897753523)
          ·
            refine ⟨11645710274538995846630285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7763806849692663897753523 11645710274538995846630285)
            ·
              refine ⟨4367141352952123442486357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11645710274538995846630285 4367141352952123442486357)
              ·
                refine ⟨51177437729907696591637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4367141352952123442486357 51177437729907696591637)
                ·
                  rfl

theorem cell22_1345514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 8].length) (baseStart_1345514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1345514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1345514 prefixEnd_1345514 := by exact prefixLift 1345514
  have htrace : WordTrace (prefixWord ++ tailWord_1345514) baseStart_1345514 baseEnd_1345514 := by
    simpa [prefixWord, tailWord_1345514, baseEnd_1345514] using wordTrace_append hprefix tailTrace_1345514
  have hstable : (prefixWord ++ tailWord_1345514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345514).length < 2 ^ (prefixWord ++ tailWord_1345514).sum := by decide
  have hdescent : baseEnd_1345514 < baseStart_1345514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345544 : List Nat := [2, 1, 3, 2, 1, 2, 2, 1, 2, 6]
def baseStart_1345544 : Nat := 118140960795 + 1345544 * 2 ^ 59
def prefixEnd_1345544 : Nat := 4983230072969 + 3 ^ 40 * 1345544 * 2
def baseEnd_1345544 : Nat := 460607209182259191074641

theorem tailTrace_1345544 : CollatzResearch.WordTrace tailWord_1345544 prefixEnd_1345544 460607209182259191074641 := by
  unfold tailWord_1345544
  simp only [CollatzResearch.WordTrace]
  refine ⟨24538010718665681732473843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32717347624887575643298457 24538010718665681732473843)
  ·
    refine ⟨36807016077998522598710765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24538010718665681732473843 36807016077998522598710765)
    ·
      refine ⟨13802631029249445974516537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36807016077998522598710765 13802631029249445974516537)
      ·
        refine ⟨10351973271937084480887403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13802631029249445974516537 10351973271937084480887403)
        ·
          refine ⟨15527959907905626721331105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10351973271937084480887403 15527959907905626721331105)
          ·
            refine ⟨11645969930929220040998329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15527959907905626721331105 11645969930929220040998329)
            ·
              refine ⟨8734477448196915030748747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11645969930929220040998329 8734477448196915030748747)
              ·
                refine ⟨13101716172295372546123121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8734477448196915030748747 13101716172295372546123121)
                ·
                  refine ⟨9826287129221529409592341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13101716172295372546123121 9826287129221529409592341)
                  ·
                    refine ⟨460607209182259191074641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9826287129221529409592341 460607209182259191074641)
                    ·
                      rfl

theorem cell22_1345544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_1345544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1345544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1345544 prefixEnd_1345544 := by exact prefixLift 1345544
  have htrace : WordTrace (prefixWord ++ tailWord_1345544) baseStart_1345544 baseEnd_1345544 := by
    simpa [prefixWord, tailWord_1345544, baseEnd_1345544] using wordTrace_append hprefix tailTrace_1345544
  have hstable : (prefixWord ++ tailWord_1345544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345544).length < 2 ^ (prefixWord ++ tailWord_1345544).sum := by decide
  have hdescent : baseEnd_1345544 < baseStart_1345544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345593 : List Nat := [1, 2, 1, 5, 3, 1, 2, 2, 5]
def baseStart_1345593 : Nat := 118140960795 + 1345593 * 2 ^ 59
def prefixEnd_1345593 : Nat := 4983230072969 + 3 ^ 40 * 1345593 * 2
def baseEnd_1345593 : Nat := 153541327627879798866497

theorem tailTrace_1345593 : CollatzResearch.WordTrace tailWord_1345593 prefixEnd_1345593 153541327627879798866497 := by
  unfold tailWord_1345593
  simp only [CollatzResearch.WordTrace]
  refine ⟨49077808614153844833481433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32718539076102563222320955 49077808614153844833481433)
  ·
    refine ⟨36808356460615383625111075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49077808614153844833481433 36808356460615383625111075)
    ·
      refine ⟨55212534690923075437666613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36808356460615383625111075 55212534690923075437666613)
      ·
        refine ⟨5176175127274038322281245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55212534690923075437666613 5176175127274038322281245)
        ·
          refine ⟨1941065672727764370855467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5176175127274038322281245 1941065672727764370855467)
          ·
            refine ⟨2911598509091646556283201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1941065672727764370855467 2911598509091646556283201)
            ·
              refine ⟨2183698881818734917212401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2911598509091646556283201 2183698881818734917212401)
              ·
                refine ⟨1637774161364051187909301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2183698881818734917212401 1637774161364051187909301)
                ·
                  refine ⟨153541327627879798866497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1637774161364051187909301 153541327627879798866497)
                  ·
                    rfl

theorem cell22_1345593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 2, 5].length) (baseStart_1345593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1345593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1345593 prefixEnd_1345593 := by exact prefixLift 1345593
  have htrace : WordTrace (prefixWord ++ tailWord_1345593) baseStart_1345593 baseEnd_1345593 := by
    simpa [prefixWord, tailWord_1345593, baseEnd_1345593] using wordTrace_append hprefix tailTrace_1345593
  have hstable : (prefixWord ++ tailWord_1345593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345593).length < 2 ^ (prefixWord ++ tailWord_1345593).sum := by decide
  have hdescent : baseEnd_1345593 < baseStart_1345593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345621 : List Nat := [1, 3, 2, 2, 1, 4, 1, 2, 6]
def baseStart_1345621 : Nat := 118140960795 + 1345621 * 2 ^ 59
def prefixEnd_1345621 : Nat := 4983230072969 + 3 ^ 40 * 1345621 * 2
def baseEnd_1345621 : Nat := 153544522618618885633135

theorem tailTrace_1345621 : CollatzResearch.WordTrace tailWord_1345621 prefixEnd_1345621 153544522618618885633135 := by
  unfold tailWord_1345621
  simp only [CollatzResearch.WordTrace]
  refine ⟨49078829858052405615500717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32719219905368270410333811 49078829858052405615500717)
  ·
    refine ⟨18404561196769652105812769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49078829858052405615500717 18404561196769652105812769)
    ·
      refine ⟨13803420897577239079359577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18404561196769652105812769 13803420897577239079359577)
      ·
        refine ⟨10352565673182929309519683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13803420897577239079359577 10352565673182929309519683)
        ·
          refine ⟨15528848509774393964279525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10352565673182929309519683 15528848509774393964279525)
          ·
            refine ⟨2911659095582698868302411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15528848509774393964279525 2911659095582698868302411)
            ·
              refine ⟨4367488643374048302453617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2911659095582698868302411 4367488643374048302453617)
              ·
                refine ⟨3275616482530536226840213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4367488643374048302453617 3275616482530536226840213)
                ·
                  refine ⟨153544522618618885633135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3275616482530536226840213 153544522618618885633135)
                  ·
                    rfl

theorem cell22_1345621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 2, 6].length) (baseStart_1345621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1345621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1345621 prefixEnd_1345621 := by exact prefixLift 1345621
  have htrace : WordTrace (prefixWord ++ tailWord_1345621) baseStart_1345621 baseEnd_1345621 := by
    simpa [prefixWord, tailWord_1345621, baseEnd_1345621] using wordTrace_append hprefix tailTrace_1345621
  have hstable : (prefixWord ++ tailWord_1345621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345621).length < 2 ^ (prefixWord ++ tailWord_1345621).sum := by decide
  have hdescent : baseEnd_1345621 < baseStart_1345621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345636 : List Nat := [2, 3, 1, 1, 2, 1, 4, 2, 1, 5]
def baseStart_1345636 : Nat := 118140960795 + 1345636 * 2 ^ 59
def prefixEnd_1345636 : Nat := 4983230072969 + 3 ^ 40 * 1345636 * 2
def baseEnd_1345636 : Nat := 460638702662401617774359

theorem tailTrace_1345636 : CollatzResearch.WordTrace tailWord_1345636 prefixEnd_1345636 460638702662401617774359 := by
  unfold tailWord_1345636
  simp only [CollatzResearch.WordTrace]
  refine ⟨24539688476499031588648381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32719584635332042118197841 24539688476499031588648381)
  ·
    refine ⟨9202383178687136845743143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24539688476499031588648381 9202383178687136845743143)
    ·
      refine ⟨13803574768030705268614715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9202383178687136845743143 13803574768030705268614715)
      ·
        refine ⟨20705362152046057902922073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13803574768030705268614715 20705362152046057902922073)
        ·
          refine ⟨15529021614034543427191555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20705362152046057902922073 15529021614034543427191555)
          ·
            refine ⟨23293532421051815140787333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15529021614034543427191555 23293532421051815140787333)
            ·
              refine ⟨4367537328947215338897625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23293532421051815140787333 4367537328947215338897625)
              ·
                refine ⟨3275652996710411504173219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4367537328947215338897625 3275652996710411504173219)
                ·
                  refine ⟨4913479495065617256259829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3275652996710411504173219 4913479495065617256259829)
                  ·
                    refine ⟨460638702662401617774359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4913479495065617256259829 460638702662401617774359)
                    ·
                      rfl

theorem cell22_1345636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_1345636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1345636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1345636 prefixEnd_1345636 := by exact prefixLift 1345636
  have htrace : WordTrace (prefixWord ++ tailWord_1345636) baseStart_1345636 baseEnd_1345636 := by
    simpa [prefixWord, tailWord_1345636, baseEnd_1345636] using wordTrace_append hprefix tailTrace_1345636
  have hstable : (prefixWord ++ tailWord_1345636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345636).length < 2 ^ (prefixWord ++ tailWord_1345636).sum := by decide
  have hdescent : baseEnd_1345636 < baseStart_1345636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345649 : List Nat := [1, 2, 2, 2, 1, 1, 13]
def baseStart_1345649 : Nat := 118140960795 + 1345649 * 2 ^ 59
def prefixEnd_1345649 : Nat := 4983230072969 + 3 ^ 40 * 1345649 * 2
def baseEnd_1345649 : Nat := 17060857512150885822197

theorem tailTrace_1345649 : CollatzResearch.WordTrace tailWord_1345649 prefixEnd_1345649 17060857512150885822197 := by
  unfold tailWord_1345649
  simp only [CollatzResearch.WordTrace]
  refine ⟨49079851101950966397520001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32719900734633977598346667 49079851101950966397520001)
  ·
    refine ⟨36809888326463224798140001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49079851101950966397520001 36809888326463224798140001)
    ·
      refine ⟨27607416244847418598605001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36809888326463224798140001 27607416244847418598605001)
      ·
        refine ⟨20705562183635563948953751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27607416244847418598605001 20705562183635563948953751)
        ·
          refine ⟨31058343275453345923430627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20705562183635563948953751 31058343275453345923430627)
          ·
            refine ⟨46587514913180018885145941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31058343275453345923430627 46587514913180018885145941)
            ·
              refine ⟨17060857512150885822197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 46587514913180018885145941 17060857512150885822197)
              ·
                rfl

theorem cell22_1345649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 13].length) (baseStart_1345649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1345649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1345649 prefixEnd_1345649 := by exact prefixLift 1345649
  have htrace : WordTrace (prefixWord ++ tailWord_1345649) baseStart_1345649 baseEnd_1345649 := by
    simpa [prefixWord, tailWord_1345649, baseEnd_1345649] using wordTrace_append hprefix tailTrace_1345649
  have hstable : (prefixWord ++ tailWord_1345649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345649).length < 2 ^ (prefixWord ++ tailWord_1345649).sum := by decide
  have hdescent : baseEnd_1345649 < baseStart_1345649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345711 : List Nat := [1, 1, 2, 1, 2, 3, 1, 6, 5]
def baseStart_1345711 : Nat := 118140960795 + 1345711 * 2 ^ 59
def prefixEnd_1345711 : Nat := 4983230072969 + 3 ^ 40 * 1345711 * 2
def baseEnd_1345711 : Nat := 153554792231708807383043

theorem tailTrace_1345711 : CollatzResearch.WordTrace tailWord_1345711 prefixEnd_1345711 153554792231708807383043 := by
  unfold tailWord_1345711
  simp only [CollatzResearch.WordTrace]
  refine ⟨49082112427726350986276987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32721408285150900657517991 49082112427726350986276987)
  ·
    refine ⟨73623168641589526479415481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49082112427726350986276987 73623168641589526479415481)
    ·
      refine ⟨55217376481192144859561611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73623168641589526479415481 55217376481192144859561611)
      ·
        refine ⟨82826064721788217289342417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55217376481192144859561611 82826064721788217289342417)
        ·
          refine ⟨62119548541341162967006813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82826064721788217289342417 62119548541341162967006813)
          ·
            refine ⟨23294830703002936112627555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62119548541341162967006813 23294830703002936112627555)
            ·
              refine ⟨34942246054504404168941333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23294830703002936112627555 34942246054504404168941333)
              ·
                refine ⟨1637917783804893945419125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34942246054504404168941333 1637917783804893945419125)
                ·
                  refine ⟨153554792231708807383043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1637917783804893945419125 153554792231708807383043)
                  ·
                    rfl

theorem cell22_1345711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 6, 5].length) (baseStart_1345711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1345711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1345711 prefixEnd_1345711 := by exact prefixLift 1345711
  have htrace : WordTrace (prefixWord ++ tailWord_1345711) baseStart_1345711 baseEnd_1345711 := by
    simpa [prefixWord, tailWord_1345711, baseEnd_1345711] using wordTrace_append hprefix tailTrace_1345711
  have hstable : (prefixWord ++ tailWord_1345711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345711).length < 2 ^ (prefixWord ++ tailWord_1345711).sum := by decide
  have hdescent : baseEnd_1345711 < baseStart_1345711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345728 : List Nat := [2, 1, 1, 2, 5, 2, 1, 3, 5]
def baseStart_1345728 : Nat := 118140960795 + 1345728 * 2 ^ 59
def prefixEnd_1345728 : Nat := 4983230072969 + 3 ^ 40 * 1345728 * 2
def baseEnd_1345728 : Nat := 153556732047514681491359

theorem tailTrace_1345728 : CollatzResearch.WordTrace tailWord_1345728 prefixEnd_1345728 153556732047514681491359 := by
  unfold tailWord_1345728
  simp only [CollatzResearch.WordTrace]
  refine ⟨24541366234332381444822919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32721821645776508593097225 24541366234332381444822919)
  ·
    refine ⟨36812049351498572167234379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24541366234332381444822919 36812049351498572167234379)
    ·
      refine ⟨55218074027247858250851569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36812049351498572167234379 55218074027247858250851569)
      ·
        refine ⟨41413555520435893688138677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55218074027247858250851569 41413555520435893688138677)
        ·
          refine ⟨3882520830040865033263001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41413555520435893688138677 3882520830040865033263001)
          ·
            refine ⟨2911890622530648774947251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3882520830040865033263001 2911890622530648774947251)
            ·
              refine ⟨4367835933795973162420877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2911890622530648774947251 4367835933795973162420877)
              ·
                refine ⟨1637938475173489935907829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4367835933795973162420877 1637938475173489935907829)
                ·
                  refine ⟨153556732047514681491359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1637938475173489935907829 153556732047514681491359)
                  ·
                    rfl

theorem cell22_1345728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 3, 5].length) (baseStart_1345728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1345728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1345728 prefixEnd_1345728 := by exact prefixLift 1345728
  have htrace : WordTrace (prefixWord ++ tailWord_1345728) baseStart_1345728 baseEnd_1345728 := by
    simpa [prefixWord, tailWord_1345728, baseEnd_1345728] using wordTrace_append hprefix tailTrace_1345728
  have hstable : (prefixWord ++ tailWord_1345728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345728).length < 2 ^ (prefixWord ++ tailWord_1345728).sum := by decide
  have hdescent : baseEnd_1345728 < baseStart_1345728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345771 : List Nat := [1, 1, 1, 1, 2, 5, 1, 2, 3, 5]
def baseStart_1345771 : Nat := 118140960795 + 1345771 * 2 ^ 59
def prefixEnd_1345771 : Nat := 4983230072969 + 3 ^ 40 * 1345771 * 2
def baseEnd_1345771 : Nat := 460684915921306265648945

theorem tailTrace_1345771 : CollatzResearch.WordTrace tailWord_1345771 prefixEnd_1345771 460684915921306265648945 := by
  unfold tailWord_1345771
  simp only [CollatzResearch.WordTrace]
  refine ⟨49084300807508981233461167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32722867205005987488974111 49084300807508981233461167)
  ·
    refine ⟨73626451211263471850191751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49084300807508981233461167 73626451211263471850191751)
    ·
      refine ⟨110439676816895207775287627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73626451211263471850191751 110439676816895207775287627)
      ·
        refine ⟨165659515225342811662931441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110439676816895207775287627 165659515225342811662931441)
        ·
          refine ⟨124244636419007108747198581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165659515225342811662931441 124244636419007108747198581)
          ·
            refine ⟨11647934664281916445049867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 124244636419007108747198581 11647934664281916445049867)
            ·
              refine ⟨17471901996422874667574801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11647934664281916445049867 17471901996422874667574801)
              ·
                refine ⟨13103926497317156000681101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17471901996422874667574801 13103926497317156000681101)
                ·
                  refine ⟨4913972436493933500255413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13103926497317156000681101 4913972436493933500255413)
                  ·
                    refine ⟨460684915921306265648945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4913972436493933500255413 460684915921306265648945)
                    ·
                      rfl

theorem cell22_1345771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 3, 5].length) (baseStart_1345771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1345771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1345771 prefixEnd_1345771 := by exact prefixLift 1345771
  have htrace : WordTrace (prefixWord ++ tailWord_1345771) baseStart_1345771 baseEnd_1345771 := by
    simpa [prefixWord, tailWord_1345771, baseEnd_1345771] using wordTrace_append hprefix tailTrace_1345771
  have hstable : (prefixWord ++ tailWord_1345771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345771).length < 2 ^ (prefixWord ++ tailWord_1345771).sum := by decide
  have hdescent : baseEnd_1345771 < baseStart_1345771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345788 : List Nat := [2, 2, 2, 1, 4, 1, 1, 3, 1, 5]
def baseStart_1345788 : Nat := 118140960795 + 1345788 * 2 ^ 59
def prefixEnd_1345788 : Nat := 4983230072969 + 3 ^ 40 * 1345788 * 2
def baseEnd_1345788 : Nat := 460690735368723887973893

theorem tailTrace_1345788 : CollatzResearch.WordTrace tailWord_1345788 prefixEnd_1345788 460690735368723887973893 := by
  unfold tailWord_1345788
  simp only [CollatzResearch.WordTrace]
  refine ⟨24542460424223696568415009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32723280565631595424553345 24542460424223696568415009)
  ·
    refine ⟨18406845318167772426311257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24542460424223696568415009 18406845318167772426311257)
    ·
      refine ⟨13805133988625829319733443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18406845318167772426311257 13805133988625829319733443)
      ·
        refine ⟨20707700982938743979600165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13805133988625829319733443 20707700982938743979600165)
        ·
          refine ⟨3882693934301014496175031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20707700982938743979600165 3882693934301014496175031)
          ·
            refine ⟨5824040901451521744262547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3882693934301014496175031 5824040901451521744262547)
            ·
              refine ⟨8736061352177282616393821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5824040901451521744262547 8736061352177282616393821)
              ·
                refine ⟨3276023007066480981147683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8736061352177282616393821 3276023007066480981147683)
                ·
                  refine ⟨4914034510599721471721525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3276023007066480981147683 4914034510599721471721525)
                  ·
                    refine ⟨460690735368723887973893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4914034510599721471721525 460690735368723887973893)
                    ·
                      rfl

theorem cell22_1345788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_1345788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1345788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1345788 prefixEnd_1345788 := by exact prefixLift 1345788
  have htrace : WordTrace (prefixWord ++ tailWord_1345788) baseStart_1345788 baseEnd_1345788 := by
    simpa [prefixWord, tailWord_1345788, baseEnd_1345788] using wordTrace_append hprefix tailTrace_1345788
  have hstable : (prefixWord ++ tailWord_1345788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345788).length < 2 ^ (prefixWord ++ tailWord_1345788).sum := by decide
  have hdescent : baseEnd_1345788 < baseStart_1345788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345818 : List Nat := [3, 1, 1, 3, 4, 1, 9]
def baseStart_1345818 : Nat := 118140960795 + 1345818 * 2 ^ 59
def prefixEnd_1345818 : Nat := 4983230072969 + 3 ^ 40 * 1345818 * 2
def baseEnd_1345818 : Nat := 17063000184511622582363

theorem tailTrace_1345818 : CollatzResearch.WordTrace tailWord_1345818 prefixEnd_1345818 17063000184511622582363 := by
  unfold tailWord_1345818
  simp only [CollatzResearch.WordTrace]
  refine ⟨12271503759584677065105527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32724010025559138840281405 12271503759584677065105527)
  ·
    refine ⟨18407255639377015597658291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12271503759584677065105527 18407255639377015597658291)
    ·
      refine ⟨27610883459065523396487437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18407255639377015597658291 27610883459065523396487437)
      ·
        refine ⟨10354081297149571273682789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27610883459065523396487437 10354081297149571273682789)
        ·
          refine ⟨1941390243215544613815523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10354081297149571273682789 1941390243215544613815523)
          ·
            refine ⟨2912085364823316920723285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1941390243215544613815523 2912085364823316920723285)
            ·
              refine ⟨17063000184511622582363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2912085364823316920723285 17063000184511622582363)
              ·
                rfl

theorem cell22_1345818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 9].length) (baseStart_1345818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1345818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1345818 prefixEnd_1345818 := by exact prefixLift 1345818
  have htrace : WordTrace (prefixWord ++ tailWord_1345818) baseStart_1345818 baseEnd_1345818 := by
    simpa [prefixWord, tailWord_1345818, baseEnd_1345818] using wordTrace_append hprefix tailTrace_1345818
  have hstable : (prefixWord ++ tailWord_1345818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345818).length < 2 ^ (prefixWord ++ tailWord_1345818).sum := by decide
  have hdescent : baseEnd_1345818 < baseStart_1345818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345850 : List Nat := [3, 1, 1, 1, 4, 2, 2, 2, 3, 3]
def baseStart_1345850 : Nat := 118140960795 + 1345850 * 2 ^ 59
def prefixEnd_1345850 : Nat := 4983230072969 + 3 ^ 40 * 1345850 * 2
def baseEnd_1345850 : Nat := 460711959235776392923703

theorem tailTrace_1345850 : CollatzResearch.WordTrace tailWord_1345850 prefixEnd_1345850 460711959235776392923703 := by
  unfold tailWord_1345850
  simp only [CollatzResearch.WordTrace]
  refine ⟨12271795543555694431396751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32724788116148518483724669 12271795543555694431396751)
  ·
    refine ⟨18407693315333541647095127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12271795543555694431396751 18407693315333541647095127)
    ·
      refine ⟨27611539973000312470642691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18407693315333541647095127 27611539973000312470642691)
      ·
        refine ⟨41417309959500468705964037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27611539973000312470642691 41417309959500468705964037)
        ·
          refine ⟨7765745617406337882368257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41417309959500468705964037 7765745617406337882368257)
          ·
            refine ⟨5824309213054753411776193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7765745617406337882368257 5824309213054753411776193)
            ·
              refine ⟨4368231909791065058832145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5824309213054753411776193 4368231909791065058832145)
              ·
                refine ⟨3276173932343298794124109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4368231909791065058832145 3276173932343298794124109)
                ·
                  refine ⟨1228565224628737047796541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3276173932343298794124109 1228565224628737047796541)
                  ·
                    refine ⟨460711959235776392923703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1228565224628737047796541 460711959235776392923703)
                    ·
                      rfl

theorem cell22_1345850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 2, 3, 3].length) (baseStart_1345850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1345850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1345850 prefixEnd_1345850 := by exact prefixLift 1345850
  have htrace : WordTrace (prefixWord ++ tailWord_1345850) baseStart_1345850 baseEnd_1345850 := by
    simpa [prefixWord, tailWord_1345850, baseEnd_1345850] using wordTrace_append hprefix tailTrace_1345850
  have hstable : (prefixWord ++ tailWord_1345850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345850).length < 2 ^ (prefixWord ++ tailWord_1345850).sum := by decide
  have hdescent : baseEnd_1345850 < baseStart_1345850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345886 : List Nat := [4, 4, 2, 1, 1, 1, 2, 7]
def baseStart_1345886 : Nat := 118140960795 + 1345886 * 2 ^ 59
def prefixEnd_1345886 : Nat := 4983230072969 + 3 ^ 40 * 1345886 * 2
def baseEnd_1345886 : Nat := 51191586974609366558177

theorem tailTrace_1345886 : CollatzResearch.WordTrace tailWord_1345886 prefixEnd_1345886 51191586974609366558177 := by
  unfold tailWord_1345886
  simp only [CollatzResearch.WordTrace]
  refine ⟨6136061900261544484237189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32725663468061570582598341 6136061900261544484237189)
  ·
    refine ⟨1150511606299039590794473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6136061900261544484237189 1150511606299039590794473)
    ·
      refine ⟨862883704724279693095855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1150511606299039590794473 862883704724279693095855)
      ·
        refine ⟨1294325557086419539643783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 862883704724279693095855 1294325557086419539643783)
        ·
          refine ⟨1941488335629629309465675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1294325557086419539643783 1941488335629629309465675)
          ·
            refine ⟨2912232503444443964198513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1941488335629629309465675 2912232503444443964198513)
            ·
              refine ⟨2184174377583332973148885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2912232503444443964198513 2184174377583332973148885)
              ·
                refine ⟨51191586974609366558177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2184174377583332973148885 51191586974609366558177)
                ·
                  rfl

theorem cell22_1345886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 7].length) (baseStart_1345886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1345886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1345886 prefixEnd_1345886 := by exact prefixLift 1345886
  have htrace : WordTrace (prefixWord ++ tailWord_1345886) baseStart_1345886 baseEnd_1345886 := by
    simpa [prefixWord, tailWord_1345886, baseEnd_1345886] using wordTrace_append hprefix tailTrace_1345886
  have hstable : (prefixWord ++ tailWord_1345886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345886).length < 2 ^ (prefixWord ++ tailWord_1345886).sum := by decide
  have hdescent : baseEnd_1345886 < baseStart_1345886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345925 : List Nat := [1, 3, 1, 1, 3, 1, 1, 7, 4]
def baseStart_1345925 : Nat := 118140960795 + 1345925 * 2 ^ 59
def prefixEnd_1345925 : Nat := 4983230072969 + 3 ^ 40 * 1345925 * 2
def baseEnd_1345925 : Nat := 153579211089500399099491

theorem tailTrace_1345925 : CollatzResearch.WordTrace tailWord_1345925 prefixEnd_1345925 153579211089500399099491 := by
  unfold tailWord_1345925
  simp only [CollatzResearch.WordTrace]
  refine ⟨49089917648951065534567229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32726611765967377023044819 49089917648951065534567229)
  ·
    refine ⟨18408719118356649575462711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49089917648951065534567229 18408719118356649575462711)
    ·
      refine ⟨27613078677534974363194067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18408719118356649575462711 27613078677534974363194067)
      ·
        refine ⟨41419618016302461544791101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27613078677534974363194067 41419618016302461544791101)
        ·
          refine ⟨15532356756113423079296663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41419618016302461544791101 15532356756113423079296663)
          ·
            refine ⟨23298535134170134618944995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15532356756113423079296663 23298535134170134618944995)
            ·
              refine ⟨34947802701255201928417493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23298535134170134618944995 34947802701255201928417493)
              ·
                refine ⟨819089125810668795197285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 34947802701255201928417493 819089125810668795197285)
                ·
                  refine ⟨153579211089500399099491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 819089125810668795197285 153579211089500399099491)
                  ·
                    rfl

theorem cell22_1345925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 7, 4].length) (baseStart_1345925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1345925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1345925 prefixEnd_1345925 := by exact prefixLift 1345925
  have htrace : WordTrace (prefixWord ++ tailWord_1345925) baseStart_1345925 baseEnd_1345925 := by
    simpa [prefixWord, tailWord_1345925, baseEnd_1345925] using wordTrace_append hprefix tailTrace_1345925
  have hstable : (prefixWord ++ tailWord_1345925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345925).length < 2 ^ (prefixWord ++ tailWord_1345925).sum := by decide
  have hdescent : baseEnd_1345925 < baseStart_1345925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345927 : List Nat := [1, 1, 4, 2, 2, 1, 5, 1, 1, 4]
def baseStart_1345927 : Nat := 118140960795 + 1345927 * 2 ^ 59
def prefixEnd_1345927 : Nat := 4983230072969 + 3 ^ 40 * 1345927 * 2
def baseEnd_1345927 : Nat := 460738317909373858748467

theorem tailTrace_1345927 : CollatzResearch.WordTrace tailWord_1345927 prefixEnd_1345927 460738317909373858748467 := by
  unfold tailWord_1345927
  simp only [CollatzResearch.WordTrace]
  refine ⟨49089990594943819876140035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32726660396629213250760023 49089990594943819876140035)
  ·
    refine ⟨73634985892415729814210053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49089990594943819876140035 73634985892415729814210053)
    ·
      refine ⟨13806559854827949340164385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73634985892415729814210053 13806559854827949340164385)
      ·
        refine ⟨10354919891120962005123289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13806559854827949340164385 10354919891120962005123289)
        ·
          refine ⟨7766189918340721503842467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10354919891120962005123289 7766189918340721503842467)
          ·
            refine ⟨11649284877511082255763701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7766189918340721503842467 11649284877511082255763701)
            ·
              refine ⟨1092120457266663961477847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11649284877511082255763701 1092120457266663961477847)
              ·
                refine ⟨1638180685899995942216771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1092120457266663961477847 1638180685899995942216771)
                ·
                  refine ⟨2457271028849993913325157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1638180685899995942216771 2457271028849993913325157)
                  ·
                    refine ⟨460738317909373858748467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2457271028849993913325157 460738317909373858748467)
                    ·
                      rfl

theorem cell22_1345927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5, 1, 1, 4].length) (baseStart_1345927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1345927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1345927 prefixEnd_1345927 := by exact prefixLift 1345927
  have htrace : WordTrace (prefixWord ++ tailWord_1345927) baseStart_1345927 baseEnd_1345927 := by
    simpa [prefixWord, tailWord_1345927, baseEnd_1345927] using wordTrace_append hprefix tailTrace_1345927
  have hstable : (prefixWord ++ tailWord_1345927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345927).length < 2 ^ (prefixWord ++ tailWord_1345927).sum := by decide
  have hdescent : baseEnd_1345927 < baseStart_1345927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345970 : List Nat := [3, 2, 1, 1, 1, 1, 7, 6]
def baseStart_1345970 : Nat := 118140960795 + 1345970 * 2 ^ 59
def prefixEnd_1345970 : Nat := 4983230072969 + 3 ^ 40 * 1345970 * 2
def baseEnd_1345970 : Nat := 51194781965348453324815

theorem tailTrace_1345970 : CollatzResearch.WordTrace tailWord_1345970 prefixEnd_1345970 51194781965348453324815 := by
  unfold tailWord_1345970
  simp only [CollatzResearch.WordTrace]
  refine ⟨12272889733447009554988841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32727705955858692146636909 12272889733447009554988841)
  ·
    refine ⟨9204667300085257166241631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12272889733447009554988841 9204667300085257166241631)
    ·
      refine ⟨13807000950127885749362447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9204667300085257166241631 13807000950127885749362447)
      ·
        refine ⟨20710501425191828624043671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13807000950127885749362447 20710501425191828624043671)
        ·
          refine ⟨31065752137787742936065507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20710501425191828624043671 31065752137787742936065507)
          ·
            refine ⟨46598628206681614404098261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31065752137787742936065507 46598628206681614404098261)
            ·
              refine ⟨1092155348594100337596053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 46598628206681614404098261 1092155348594100337596053)
              ·
                refine ⟨51194781965348453324815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1092155348594100337596053 51194781965348453324815)
                ·
                  rfl

theorem cell22_1345970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7, 6].length) (baseStart_1345970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1345970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1345970 prefixEnd_1345970 := by exact prefixLift 1345970
  have htrace : WordTrace (prefixWord ++ tailWord_1345970) baseStart_1345970 baseEnd_1345970 := by
    simpa [prefixWord, tailWord_1345970, baseEnd_1345970] using wordTrace_append hprefix tailTrace_1345970
  have hstable : (prefixWord ++ tailWord_1345970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345970).length < 2 ^ (prefixWord ++ tailWord_1345970).sum := by decide
  have hdescent : baseEnd_1345970 < baseStart_1345970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346109 : List Nat := [1, 4, 1, 3, 2, 1, 1, 4, 2, 3]
def baseStart_1346109 : Nat := 118140960795 + 1346109 * 2 ^ 59
def prefixEnd_1346109 : Nat := 4983230072969 + 3 ^ 40 * 1346109 * 2
def baseEnd_1346109 : Nat := 460800620228786050697909

theorem tailTrace_1346109 : CollatzResearch.WordTrace tailWord_1346109 prefixEnd_1346109 460800620228786050697909 := by
  unfold tailWord_1346109
  simp only [CollatzResearch.WordTrace]
  refine ⟨49096628680284464959265381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32731085786856309972843587 49096628680284464959265381)
  ·
    refine ⟨9205617877553337179862259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49096628680284464959265381 9205617877553337179862259)
    ·
      refine ⟨13808426816330005769793389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9205617877553337179862259 13808426816330005769793389)
      ·
        refine ⟨5178160056123752163672521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13808426816330005769793389 5178160056123752163672521)
        ·
          refine ⟨3883620042092814122754391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5178160056123752163672521 3883620042092814122754391)
          ·
            refine ⟨5825430063139221184131587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3883620042092814122754391 5825430063139221184131587)
            ·
              refine ⟨8738145094708831776197381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5825430063139221184131587 8738145094708831776197381)
              ·
                refine ⟨1638402205257905958037009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8738145094708831776197381 1638402205257905958037009)
                ·
                  refine ⟨1228801653943429468527757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1638402205257905958037009 1228801653943429468527757)
                  ·
                    refine ⟨460800620228786050697909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1228801653943429468527757 460800620228786050697909)
                    ·
                      rfl

theorem cell22_1346109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 4, 2, 3].length) (baseStart_1346109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1346109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1346109 prefixEnd_1346109 := by exact prefixLift 1346109
  have htrace : WordTrace (prefixWord ++ tailWord_1346109) baseStart_1346109 baseEnd_1346109 := by
    simpa [prefixWord, tailWord_1346109, baseEnd_1346109] using wordTrace_append hprefix tailTrace_1346109
  have hstable : (prefixWord ++ tailWord_1346109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346109).length < 2 ^ (prefixWord ++ tailWord_1346109).sum := by decide
  have hdescent : baseEnd_1346109 < baseStart_1346109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346122 : List Nat := [3, 1, 2, 1, 1, 6, 1, 7]
def baseStart_1346122 : Nat := 118140960795 + 1346122 * 2 ^ 59
def prefixEnd_1346122 : Nat := 4983230072969 + 3 ^ 40 * 1346122 * 2
def baseEnd_1346122 : Nat := 51200563377162038902541

theorem tailTrace_1346122 : CollatzResearch.WordTrace tailWord_1346122 prefixEnd_1346122 51200563377162038902541 := by
  unfold tailWord_1346122
  simp only [CollatzResearch.WordTrace]
  refine ⟨12274275707309342044872155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32731401886158245452992413 12274275707309342044872155)
  ·
    refine ⟨18411413560964013067308233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12274275707309342044872155 18411413560964013067308233)
    ·
      refine ⟨13808560170723009800481175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18411413560964013067308233 13808560170723009800481175)
      ·
        refine ⟨20712840256084514700721763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13808560170723009800481175 20712840256084514700721763)
        ·
          refine ⟨31069260384126772051082645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20712840256084514700721763 31069260384126772051082645)
          ·
            refine ⟨1456371580505942439894499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 31069260384126772051082645 1456371580505942439894499)
            ·
              refine ⟨2184557370758913659841749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1456371580505942439894499 2184557370758913659841749)
              ·
                refine ⟨51200563377162038902541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2184557370758913659841749 51200563377162038902541)
                ·
                  rfl

theorem cell22_1346122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 7].length) (baseStart_1346122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1346122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1346122 prefixEnd_1346122 := by exact prefixLift 1346122
  have htrace : WordTrace (prefixWord ++ tailWord_1346122) baseStart_1346122 baseEnd_1346122 := by
    simpa [prefixWord, tailWord_1346122, baseEnd_1346122] using wordTrace_append hprefix tailTrace_1346122
  have hstable : (prefixWord ++ tailWord_1346122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346122).length < 2 ^ (prefixWord ++ tailWord_1346122).sum := by decide
  have hdescent : baseEnd_1346122 < baseStart_1346122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346135 : List Nat := [1, 1, 3, 2, 2, 2, 1, 2, 2, 6]
def baseStart_1346135 : Nat := 118140960795 + 1346135 * 2 ^ 59
def prefixEnd_1346135 : Nat := 4983230072969 + 3 ^ 40 * 1346135 * 2
def baseEnd_1346135 : Nat := 460809520560130649547829

theorem tailTrace_1346135 : CollatzResearch.WordTrace tailWord_1346135 prefixEnd_1346135 460809520560130649547829 := by
  unfold tailWord_1346135
  simp only [CollatzResearch.WordTrace]
  refine ⟨49097576978190271399711859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32731717985460180933141239 49097576978190271399711859)
  ·
    refine ⟨73646365467285407099567789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49097576978190271399711859 73646365467285407099567789)
    ·
      refine ⟨27617387050232027662337921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73646365467285407099567789 27617387050232027662337921)
      ·
        refine ⟨20713040287674020746753441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27617387050232027662337921 20713040287674020746753441)
        ·
          refine ⟨15534780215755515560065081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20713040287674020746753441 15534780215755515560065081)
          ·
            refine ⟨11651085161816636670048811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15534780215755515560065081 11651085161816636670048811)
            ·
              refine ⟨17476627742724955005073217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11651085161816636670048811 17476627742724955005073217)
              ·
                refine ⟨13107470807043716253804913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17476627742724955005073217 13107470807043716253804913)
                ·
                  refine ⟨9830603105282787190353685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13107470807043716253804913 9830603105282787190353685)
                  ·
                    refine ⟨460809520560130649547829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9830603105282787190353685 460809520560130649547829)
                    ·
                      rfl

theorem cell22_1346135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 6].length) (baseStart_1346135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1346135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1346135 prefixEnd_1346135 := by exact prefixLift 1346135
  have htrace : WordTrace (prefixWord ++ tailWord_1346135) baseStart_1346135 baseEnd_1346135 := by
    simpa [prefixWord, tailWord_1346135, baseEnd_1346135] using wordTrace_append hprefix tailTrace_1346135
  have hstable : (prefixWord ++ tailWord_1346135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346135).length < 2 ^ (prefixWord ++ tailWord_1346135).sum := by decide
  have hdescent : baseEnd_1346135 < baseStart_1346135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346167 : List Nat := [1, 1, 3, 1, 1, 3, 5, 2, 5]
def baseStart_1346167 : Nat := 118140960795 + 1346167 * 2 ^ 59
def prefixEnd_1346167 : Nat := 4983230072969 + 3 ^ 40 * 1346167 * 2
def baseEnd_1346167 : Nat := 153606824938031077582577

theorem tailTrace_1346167 : CollatzResearch.WordTrace tailWord_1346167 prefixEnd_1346167 153606824938031077582577 := by
  unfold tailWord_1346167
  simp only [CollatzResearch.WordTrace]
  refine ⟨49098744114074340864876755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32732496076049560576584503 49098744114074340864876755)
  ·
    refine ⟨73648116171111511297315133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49098744114074340864876755 73648116171111511297315133)
    ·
      refine ⟨27618043564166816736493175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73648116171111511297315133 27618043564166816736493175)
      ·
        refine ⟨41427065346250225104739763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27618043564166816736493175 41427065346250225104739763)
        ·
          refine ⟨62140598019375337657109645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41427065346250225104739763 62140598019375337657109645)
          ·
            refine ⟨23302724257265751621416117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62140598019375337657109645 23302724257265751621416117)
            ·
              refine ⟨2184630399118664214507761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23302724257265751621416117 2184630399118664214507761)
              ·
                refine ⟨1638472799338998160880821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2184630399118664214507761 1638472799338998160880821)
                ·
                  refine ⟨153606824938031077582577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1638472799338998160880821 153606824938031077582577)
                  ·
                    rfl

theorem cell22_1346167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 2, 5].length) (baseStart_1346167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1346167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1346167 prefixEnd_1346167 := by exact prefixLift 1346167
  have htrace : WordTrace (prefixWord ++ tailWord_1346167) baseStart_1346167 baseEnd_1346167 := by
    simpa [prefixWord, tailWord_1346167, baseEnd_1346167] using wordTrace_append hprefix tailTrace_1346167
  have hstable : (prefixWord ++ tailWord_1346167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346167).length < 2 ^ (prefixWord ++ tailWord_1346167).sum := by decide
  have hdescent : baseEnd_1346167 < baseStart_1346167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346229 : List Nat := [1, 3, 3, 3, 1, 1, 3, 1, 6]
def baseStart_1346229 : Nat := 118140960795 + 1346229 * 2 ^ 59
def prefixEnd_1346229 : Nat := 4983230072969 + 3 ^ 40 * 1346229 * 2
def baseEnd_1346229 : Nat := 153613899560381912565847

theorem tailTrace_1346229 : CollatzResearch.WordTrace tailWord_1346229 prefixEnd_1346229 153613899560381912565847 := by
  unfold tailWord_1346229
  simp only [CollatzResearch.WordTrace]
  refine ⟨49101005439849725453633741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32734003626566483635755827 49101005439849725453633741)
  ·
    refine ⟨18412877039943647045112653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49101005439849725453633741 18412877039943647045112653)
    ·
      refine ⟨6904828889978867641917245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18412877039943647045112653 6904828889978867641917245)
      ·
        refine ⟨2589310833742075365718967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6904828889978867641917245 2589310833742075365718967)
        ·
          refine ⟨3883966250613113048578451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2589310833742075365718967 3883966250613113048578451)
          ·
            refine ⟨5825949375919669572867677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3883966250613113048578451 5825949375919669572867677)
            ·
              refine ⟨2184731015969876089825379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5825949375919669572867677 2184731015969876089825379)
              ·
                refine ⟨3277096523954814134738069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2184731015969876089825379 3277096523954814134738069)
                ·
                  refine ⟨153613899560381912565847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3277096523954814134738069 153613899560381912565847)
                  ·
                    rfl

theorem cell22_1346229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 1, 6].length) (baseStart_1346229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1346229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1346229 prefixEnd_1346229 := by exact prefixLift 1346229
  have htrace : WordTrace (prefixWord ++ tailWord_1346229) baseStart_1346229 baseEnd_1346229 := by
    simpa [prefixWord, tailWord_1346229, baseEnd_1346229] using wordTrace_append hprefix tailTrace_1346229
  have hstable : (prefixWord ++ tailWord_1346229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346229).length < 2 ^ (prefixWord ++ tailWord_1346229).sum := by decide
  have hdescent : baseEnd_1346229 < baseStart_1346229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346261 : List Nat := [1, 3, 2, 5, 1, 1, 1, 2, 1, 5]
def baseStart_1346261 : Nat := 118140960795 + 1346261 * 2 ^ 59
def prefixEnd_1346261 : Nat := 4983230072969 + 3 ^ 40 * 1346261 * 2
def baseEnd_1346261 : Nat := 460852652935108320897443

theorem tailTrace_1346261 : CollatzResearch.WordTrace tailWord_1346261 prefixEnd_1346261 460852652935108320897443 := by
  unfold tailWord_1346261
  simp only [CollatzResearch.WordTrace]
  refine ⟨49102172575733794918798637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32734781717155863279199091 49102172575733794918798637)
  ·
    refine ⟨18413314715900173094549489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49102172575733794918798637 18413314715900173094549489)
    ·
      refine ⟨13809986036925129820912117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18413314715900173094549489 13809986036925129820912117)
      ·
        refine ⟨1294686190961730920710511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13809986036925129820912117 1294686190961730920710511)
        ·
          refine ⟨1942029286442596381065767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1294686190961730920710511 1942029286442596381065767)
          ·
            refine ⟨2913043929663894571598651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1942029286442596381065767 2913043929663894571598651)
            ·
              refine ⟨4369565894495841857397977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2913043929663894571598651 4369565894495841857397977)
              ·
                refine ⟨3277174420871881393048483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4369565894495841857397977 3277174420871881393048483)
                ·
                  refine ⟨4915761631307822089572725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3277174420871881393048483 4915761631307822089572725)
                  ·
                    refine ⟨460852652935108320897443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4915761631307822089572725 460852652935108320897443)
                    ·
                      rfl

theorem cell22_1346261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 2, 1, 5].length) (baseStart_1346261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1346261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1346261 prefixEnd_1346261 := by exact prefixLift 1346261
  have htrace : WordTrace (prefixWord ++ tailWord_1346261) baseStart_1346261 baseEnd_1346261 := by
    simpa [prefixWord, tailWord_1346261, baseEnd_1346261] using wordTrace_append hprefix tailTrace_1346261
  have hstable : (prefixWord ++ tailWord_1346261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346261).length < 2 ^ (prefixWord ++ tailWord_1346261).sum := by decide
  have hdescent : baseEnd_1346261 < baseStart_1346261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346280 : List Nat := [2, 1, 4, 1, 5, 1, 2, 2, 4]
def baseStart_1346280 : Nat := 118140960795 + 1346280 * 2 ^ 59
def prefixEnd_1346280 : Nat := 4983230072969 + 3 ^ 40 * 1346280 * 2
def baseEnd_1346280 : Nat := 153619719007799534890795

theorem tailTrace_1346280 : CollatzResearch.WordTrace tailWord_1346280 prefixEnd_1346280 153619719007799534890795 := by
  unfold tailWord_1346280
  simp only [CollatzResearch.WordTrace]
  refine ⟨24551432781332480581870147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32735243708443307442493529 24551432781332480581870147)
  ·
    refine ⟨36827149171998720872805221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24551432781332480581870147 36827149171998720872805221)
    ·
      refine ⟨6905090469749760163650979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36827149171998720872805221 6905090469749760163650979)
      ·
        refine ⟨10357635704624640245476469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6905090469749760163650979 10357635704624640245476469)
        ·
          refine ⟨971028347308560023013419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10357635704624640245476469 971028347308560023013419)
          ·
            refine ⟨1456542520962840034520129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 971028347308560023013419 1456542520962840034520129)
            ·
              refine ⟨1092406890722130025890097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1456542520962840034520129 1092406890722130025890097)
              ·
                refine ⟨819305168041597519417573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1092406890722130025890097 819305168041597519417573)
                ·
                  refine ⟨153619719007799534890795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 819305168041597519417573 153619719007799534890795)
                  ·
                    rfl

theorem cell22_1346280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 2, 2, 4].length) (baseStart_1346280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1346280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1346280 prefixEnd_1346280 := by exact prefixLift 1346280
  have htrace : WordTrace (prefixWord ++ tailWord_1346280) baseStart_1346280 baseEnd_1346280 := by
    simpa [prefixWord, tailWord_1346280, baseEnd_1346280] using wordTrace_append hprefix tailTrace_1346280
  have hstable : (prefixWord ++ tailWord_1346280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346280).length < 2 ^ (prefixWord ++ tailWord_1346280).sum := by decide
  have hdescent : baseEnd_1346280 < baseStart_1346280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346287 : List Nat := [1, 1, 2, 1, 5, 2, 1, 1, 2, 6]
def baseStart_1346287 : Nat := 118140960795 + 1346287 * 2 ^ 59
def prefixEnd_1346287 : Nat := 4983230072969 + 3 ^ 40 * 1346287 * 2
def baseEnd_1346287 : Nat := 460861553266452919747363

theorem tailTrace_1346287 : CollatzResearch.WordTrace tailWord_1346287 prefixEnd_1346287 460861553266452919747363 := by
  unfold tailWord_1346287
  simp only [CollatzResearch.WordTrace]
  refine ⟨49103120873639601359245115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32735413915759734239496743 49103120873639601359245115)
  ·
    refine ⟨73654681310459402038867673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49103120873639601359245115 73654681310459402038867673)
    ·
      refine ⟨55241010982844551529150755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73654681310459402038867673 55241010982844551529150755)
      ·
        refine ⟨82861516474266827293726133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55241010982844551529150755 82861516474266827293726133)
        ·
          refine ⟨7768267169462515058786825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82861516474266827293726133 7768267169462515058786825)
          ·
            refine ⟨5826200377096886294090119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7768267169462515058786825 5826200377096886294090119)
            ·
              refine ⟨8739300565645329441135179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5826200377096886294090119 8739300565645329441135179)
              ·
                refine ⟨13108950848467994161702769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8739300565645329441135179 13108950848467994161702769)
                ·
                  refine ⟨9831713136350995621277077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13108950848467994161702769 9831713136350995621277077)
                  ·
                    refine ⟨460861553266452919747363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9831713136350995621277077 460861553266452919747363)
                    ·
                      rfl

theorem cell22_1346287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 6].length) (baseStart_1346287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1346287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1346287 prefixEnd_1346287 := by exact prefixLift 1346287
  have htrace : WordTrace (prefixWord ++ tailWord_1346287) baseStart_1346287 baseEnd_1346287 := by
    simpa [prefixWord, tailWord_1346287, baseEnd_1346287] using wordTrace_append hprefix tailTrace_1346287
  have hstable : (prefixWord ++ tailWord_1346287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346287).length < 2 ^ (prefixWord ++ tailWord_1346287).sum := by decide
  have hdescent : baseEnd_1346287 < baseStart_1346287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346289 : List Nat := [1, 2, 2, 2, 2, 2, 2, 3, 3, 3]
def baseStart_1346289 : Nat := 118140960795 + 1346289 * 2 ^ 59
def prefixEnd_1346289 : Nat := 4983230072969 + 3 ^ 40 * 1346289 * 2
def baseEnd_1346289 : Nat := 460862237907325581197357

theorem tailTrace_1346289 : CollatzResearch.WordTrace tailWord_1346289 prefixEnd_1346289 460862237907325581197357 := by
  unfold tailWord_1346289
  simp only [CollatzResearch.WordTrace]
  refine ⟨49103193819632355700817921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32735462546421570467211947 49103193819632355700817921)
  ·
    refine ⟨36827395364724266775613441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49103193819632355700817921 36827395364724266775613441)
    ·
      refine ⟨27620546523543200081710081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36827395364724266775613441 27620546523543200081710081)
      ·
        refine ⟨20715409892657400061282561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27620546523543200081710081 20715409892657400061282561)
        ·
          refine ⟨15536557419493050045961921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20715409892657400061282561 15536557419493050045961921)
          ·
            refine ⟨11652418064619787534471441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15536557419493050045961921 11652418064619787534471441)
            ·
              refine ⟨8739313548464840650853581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11652418064619787534471441 8739313548464840650853581)
              ·
                refine ⟨3277242580674315244070093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8739313548464840650853581 3277242580674315244070093)
                ·
                  refine ⟨1228965967752868216526285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3277242580674315244070093 1228965967752868216526285)
                  ·
                    refine ⟨460862237907325581197357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1228965967752868216526285 460862237907325581197357)
                    ·
                      rfl

theorem cell22_1346289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 3].length) (baseStart_1346289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1346289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1346289 prefixEnd_1346289 := by exact prefixLift 1346289
  have htrace : WordTrace (prefixWord ++ tailWord_1346289) baseStart_1346289 baseEnd_1346289 := by
    simpa [prefixWord, tailWord_1346289, baseEnd_1346289] using wordTrace_append hprefix tailTrace_1346289
  have hstable : (prefixWord ++ tailWord_1346289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346289).length < 2 ^ (prefixWord ++ tailWord_1346289).sum := by decide
  have hdescent : baseEnd_1346289 < baseStart_1346289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346306 : List Nat := [3, 4, 1, 1, 1, 2, 1, 1, 5, 3]
def baseStart_1346306 : Nat := 118140960795 + 1346306 * 2 ^ 59
def prefixEnd_1346306 : Nat := 4983230072969 + 3 ^ 40 * 1346306 * 2
def baseEnd_1346306 : Nat := 460868057354743203522305

theorem tailTrace_1346306 : CollatzResearch.WordTrace tailWord_1346306 prefixEnd_1346306 460868057354743203522305 := by
  unfold tailWord_1346306
  simp only [CollatzResearch.WordTrace]
  refine ⟨12275953465142691901046693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32735875907047178402791181 12275953465142691901046693)
  ·
    refine ⟨2301741274714254731446255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12275953465142691901046693 2301741274714254731446255)
    ·
      refine ⟨3452611912071382097169383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2301741274714254731446255 3452611912071382097169383)
      ·
        refine ⟨5178917868107073145754075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3452611912071382097169383 5178917868107073145754075)
        ·
          refine ⟨7768376802160609718631113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5178917868107073145754075 7768376802160609718631113)
          ·
            refine ⟨5826282601620457288973335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7768376802160609718631113 5826282601620457288973335)
            ·
              refine ⟨8739423902430685933460003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5826282601620457288973335 8739423902430685933460003)
              ·
                refine ⟨13109135853646028900190005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8739423902430685933460003 13109135853646028900190005)
                ·
                  refine ⟨1228981486279315209392813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13109135853646028900190005 1228981486279315209392813)
                  ·
                    refine ⟨460868057354743203522305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1228981486279315209392813 460868057354743203522305)
                    ·
                      rfl

theorem cell22_1346306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_1346306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1346306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1346306 prefixEnd_1346306 := by exact prefixLift 1346306
  have htrace : WordTrace (prefixWord ++ tailWord_1346306) baseStart_1346306 baseEnd_1346306 := by
    simpa [prefixWord, tailWord_1346306, baseEnd_1346306] using wordTrace_append hprefix tailTrace_1346306
  have hstable : (prefixWord ++ tailWord_1346306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346306).length < 2 ^ (prefixWord ++ tailWord_1346306).sum := by decide
  have hdescent : baseEnd_1346306 < baseStart_1346306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346336 : List Nat := [2, 1, 1, 5, 1, 4, 1, 2, 5]
def baseStart_1346336 : Nat := 118140960795 + 1346336 * 2 ^ 59
def prefixEnd_1346336 : Nat := 4983230072969 + 3 ^ 40 * 1346336 * 2
def baseEnd_1346336 : Nat := 153626108989277708424071

theorem tailTrace_1346336 : CollatzResearch.WordTrace tailWord_1346336 prefixEnd_1346336 153626108989277708424071 := by
  unfold tailWord_1346336
  simp only [CollatzResearch.WordTrace]
  refine ⟨24552454025231041363889431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32736605366974721818519241 24552454025231041363889431)
  ·
    refine ⟨36828681037846562045834147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24552454025231041363889431 36828681037846562045834147)
    ·
      refine ⟨55243021556769843068751221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36828681037846562045834147 55243021556769843068751221)
      ·
        refine ⟨5179033270947172787695427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55243021556769843068751221 5179033270947172787695427)
        ·
          refine ⟨7768549906420759181543141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5179033270947172787695427 7768549906420759181543141)
          ·
            refine ⟨1456603107453892346539339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7768549906420759181543141 1456603107453892346539339)
            ·
              refine ⟨2184904661180838519809009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1456603107453892346539339 2184904661180838519809009)
              ·
                refine ⟨1638678495885628889856757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2184904661180838519809009 1638678495885628889856757)
                ·
                  refine ⟨153626108989277708424071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1638678495885628889856757 153626108989277708424071)
                  ·
                    rfl

theorem cell22_1346336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 2, 5].length) (baseStart_1346336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1346336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1346336 prefixEnd_1346336 := by exact prefixLift 1346336
  have htrace : WordTrace (prefixWord ++ tailWord_1346336) baseStart_1346336 baseEnd_1346336 := by
    simpa [prefixWord, tailWord_1346336, baseEnd_1346336] using wordTrace_append hprefix tailTrace_1346336
  have hstable : (prefixWord ++ tailWord_1346336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346336).length < 2 ^ (prefixWord ++ tailWord_1346336).sum := by decide
  have hdescent : baseEnd_1346336 < baseStart_1346336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346347 : List Nat := [1, 1, 1, 1, 2, 1, 2, 7, 6]
def baseStart_1346347 : Nat := 118140960795 + 1346347 * 2 ^ 59
def prefixEnd_1346347 : Nat := 4983230072969 + 3 ^ 40 * 1346347 * 2
def baseEnd_1346347 : Nat := 153627364164210921082393

theorem tailTrace_1346347 : CollatzResearch.WordTrace tailWord_1346347 prefixEnd_1346347 153627364164210921082393 := by
  unfold tailWord_1346347
  simp only [CollatzResearch.WordTrace]
  refine ⟨49105309253422231606429295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32736872835614821070952863 49105309253422231606429295)
  ·
    refine ⟨73657963880133347409643943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49105309253422231606429295 73657963880133347409643943)
    ·
      refine ⟨110486945820200021114465915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73657963880133347409643943 110486945820200021114465915)
      ·
        refine ⟨165730418730300031671698873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110486945820200021114465915 165730418730300031671698873)
        ·
          refine ⟨124297814047725023753774155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165730418730300031671698873 124297814047725023753774155)
          ·
            refine ⟨186446721071587535630661233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124297814047725023753774155 186446721071587535630661233)
            ·
              refine ⟨139835040803690651722995925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 186446721071587535630661233 139835040803690651722995925)
              ·
                refine ⟨3277383768836499649757717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 139835040803690651722995925 3277383768836499649757717)
                ·
                  refine ⟨153627364164210921082393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3277383768836499649757717 153627364164210921082393)
                  ·
                    rfl

theorem cell22_1346347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7, 6].length) (baseStart_1346347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1346347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1346347 prefixEnd_1346347 := by exact prefixLift 1346347
  have htrace : WordTrace (prefixWord ++ tailWord_1346347) baseStart_1346347 baseEnd_1346347 := by
    simpa [prefixWord, tailWord_1346347, baseEnd_1346347] using wordTrace_append hprefix tailTrace_1346347
  have hstable : (prefixWord ++ tailWord_1346347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346347).length < 2 ^ (prefixWord ++ tailWord_1346347).sum := by decide
  have hdescent : baseEnd_1346347 < baseStart_1346347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346374 : List Nat := [6, 1, 1, 2, 2, 2, 1, 3, 1, 3]
def baseStart_1346374 : Nat := 118140960795 + 1346374 * 2 ^ 59
def prefixEnd_1346374 : Nat := 4983230072969 + 3 ^ 40 * 1346374 * 2
def baseEnd_1346374 : Nat := 460891335144413692822097

theorem tailTrace_1346374 : CollatzResearch.WordTrace tailWord_1346374 prefixEnd_1346374 460891335144413692822097 := by
  unfold tailWord_1346374
  simp only [CollatzResearch.WordTrace]
  refine ⟨1534571688260137975551943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 32737529349549610145108117 1534571688260137975551943)
  ·
    refine ⟨2301857532390206963327915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1534571688260137975551943 2301857532390206963327915)
    ·
      refine ⟨3452786298585310444991873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2301857532390206963327915 3452786298585310444991873)
      ·
        refine ⟨2589589723938982833743905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3452786298585310444991873 2589589723938982833743905)
        ·
          refine ⟨1942192292954237125307929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2589589723938982833743905 1942192292954237125307929)
          ·
            refine ⟨1456644219715677843980947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1942192292954237125307929 1456644219715677843980947)
            ·
              refine ⟨2184966329573516765971421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1456644219715677843980947 2184966329573516765971421)
              ·
                refine ⟨819362373590068787239283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2184966329573516765971421 819362373590068787239283)
                ·
                  refine ⟨1229043560385103180858925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 819362373590068787239283 1229043560385103180858925)
                  ·
                    refine ⟨460891335144413692822097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1229043560385103180858925 460891335144413692822097)
                    ·
                      rfl

theorem cell22_1346374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_1346374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1346374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1346374 prefixEnd_1346374 := by exact prefixLift 1346374
  have htrace : WordTrace (prefixWord ++ tailWord_1346374) baseStart_1346374 baseEnd_1346374 := by
    simpa [prefixWord, tailWord_1346374, baseEnd_1346374] using wordTrace_append hprefix tailTrace_1346374
  have hstable : (prefixWord ++ tailWord_1346374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346374).length < 2 ^ (prefixWord ++ tailWord_1346374).sum := by decide
  have hdescent : baseEnd_1346374 < baseStart_1346374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346394 : List Nat := [3, 1, 1, 2, 1, 4, 1, 1, 4, 4]
def baseStart_1346394 : Nat := 118140960795 + 1346394 * 2 ^ 59
def prefixEnd_1346394 : Nat := 4983230072969 + 3 ^ 40 * 1346394 * 2
def baseEnd_1346394 : Nat := 460898181553140307322035

theorem tailTrace_1346394 : CollatzResearch.WordTrace tailWord_1346394 prefixEnd_1346394 460898181553140307322035 := by
  unfold tailWord_1346394
  simp only [CollatzResearch.WordTrace]
  refine ⟨12276755871062989658347559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32738015656167972422260157 12276755871062989658347559)
  ·
    refine ⟨18415133806594484487521339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12276755871062989658347559 18415133806594484487521339)
    ·
      refine ⟨27622700709891726731282009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18415133806594484487521339 27622700709891726731282009)
      ·
        refine ⟨20717025532418795048461507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27622700709891726731282009 20717025532418795048461507)
        ·
          refine ⟨31075538298628192572692261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20717025532418795048461507 31075538298628192572692261)
          ·
            refine ⟨5826663430992786107379799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31075538298628192572692261 5826663430992786107379799)
            ·
              refine ⟨8739995146489179161069699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5826663430992786107379799 8739995146489179161069699)
              ·
                refine ⟨13109992719733768741604549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8739995146489179161069699 13109992719733768741604549)
                ·
                  refine ⟨2458123634950081639050853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13109992719733768741604549 2458123634950081639050853)
                  ·
                    refine ⟨460898181553140307322035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2458123634950081639050853 460898181553140307322035)
                    ·
                      rfl

theorem cell22_1346394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 4, 4].length) (baseStart_1346394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1346394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1346394 prefixEnd_1346394 := by exact prefixLift 1346394
  have htrace : WordTrace (prefixWord ++ tailWord_1346394) baseStart_1346394 baseEnd_1346394 := by
    simpa [prefixWord, tailWord_1346394, baseEnd_1346394] using wordTrace_append hprefix tailTrace_1346394
  have hstable : (prefixWord ++ tailWord_1346394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346394).length < 2 ^ (prefixWord ++ tailWord_1346394).sum := by decide
  have hdescent : baseEnd_1346394 < baseStart_1346394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346509 : List Nat := [1, 6, 3, 1, 1, 1, 2, 1, 3, 3]
def baseStart_1346509 : Nat := 118140960795 + 1346509 * 2 ^ 59
def prefixEnd_1346509 : Nat := 4983230072969 + 3 ^ 40 * 1346509 * 2
def baseEnd_1346509 : Nat := 460937548403318340696683

theorem tailTrace_1346509 : CollatzResearch.WordTrace tailWord_1346509 prefixEnd_1346509 460937548403318340696683 := by
  unfold tailWord_1346509
  simp only [CollatzResearch.WordTrace]
  refine ⟨49111217878835333273826581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32740811919223555515884387 49111217878835333273826581)
  ·
    refine ⟨2302088338070406247210621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 49111217878835333273826581 2302088338070406247210621)
    ·
      refine ⟨863283126776402342703983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2302088338070406247210621 863283126776402342703983)
      ·
        refine ⟨1294924690164603514055975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 863283126776402342703983 1294924690164603514055975)
        ·
          refine ⟨1942387035246905271083963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1294924690164603514055975 1942387035246905271083963)
          ·
            refine ⟨2913580552870357906625945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1942387035246905271083963 2913580552870357906625945)
            ·
              refine ⟨2185185414652768429969459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2913580552870357906625945 2185185414652768429969459)
              ·
                refine ⟨3277778121979152644954189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2185185414652768429969459 3277778121979152644954189)
                ·
                  refine ⟨1229166795742182241857821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3277778121979152644954189 1229166795742182241857821)
                  ·
                    refine ⟨460937548403318340696683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1229166795742182241857821 460937548403318340696683)
                    ·
                      rfl

theorem cell22_1346509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_1346509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1346509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1346509 prefixEnd_1346509 := by exact prefixLift 1346509
  have htrace : WordTrace (prefixWord ++ tailWord_1346509) baseStart_1346509 baseEnd_1346509 := by
    simpa [prefixWord, tailWord_1346509, baseEnd_1346509] using wordTrace_append hprefix tailTrace_1346509
  have hstable : (prefixWord ++ tailWord_1346509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346509).length < 2 ^ (prefixWord ++ tailWord_1346509).sum := by decide
  have hdescent : baseEnd_1346509 < baseStart_1346509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346516 : List Nat := [2, 4, 1, 2, 1, 2, 1, 3, 6]
def baseStart_1346516 : Nat := 118140960795 + 1346516 * 2 ^ 59
def prefixEnd_1346516 : Nat := 4983230072969 + 3 ^ 40 * 1346516 * 2
def baseEnd_1346516 : Nat := 153646648215457551923887

theorem tailTrace_1346516 : CollatzResearch.WordTrace tailWord_1346516 prefixEnd_1346516 153646648215457551923887 := by
  unfold tailWord_1346516
  simp only [CollatzResearch.WordTrace]
  refine ⟨24555736594904986734665701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32740982126539982312887601 24555736594904986734665701)
  ·
    refine ⟨4604200611544685012749819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24555736594904986734665701 4604200611544685012749819)
    ·
      refine ⟨6906300917317027519124729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4604200611544685012749819 6906300917317027519124729)
      ·
        refine ⟨5179725687987770639343547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6906300917317027519124729 5179725687987770639343547)
        ·
          refine ⟨7769588531981655959015321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5179725687987770639343547 7769588531981655959015321)
          ·
            refine ⟨5827191398986241969261491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7769588531981655959015321 5827191398986241969261491)
            ·
              refine ⟨8740787098479362953892237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5827191398986241969261491 8740787098479362953892237)
              ·
                refine ⟨3277795161929761107709589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8740787098479362953892237 3277795161929761107709589)
                ·
                  refine ⟨153646648215457551923887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3277795161929761107709589 153646648215457551923887)
                  ·
                    rfl

theorem cell22_1346516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_1346516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1346516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1346516 prefixEnd_1346516 := by exact prefixLift 1346516
  have htrace : WordTrace (prefixWord ++ tailWord_1346516) baseStart_1346516 baseEnd_1346516 := by
    simpa [prefixWord, tailWord_1346516, baseEnd_1346516] using wordTrace_append hprefix tailTrace_1346516
  have hstable : (prefixWord ++ tailWord_1346516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346516).length < 2 ^ (prefixWord ++ tailWord_1346516).sum := by decide
  have hdescent : baseEnd_1346516 < baseStart_1346516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346550 : List Nat := [5, 1, 1, 1, 3, 1, 3, 3, 4]
def baseStart_1346550 : Nat := 118140960795 + 1346550 * 2 ^ 59
def prefixEnd_1346550 : Nat := 4983230072969 + 3 ^ 40 * 1346550 * 2
def baseEnd_1346550 : Nat := 153650527847069300140519

theorem tailTrace_1346550 : CollatzResearch.WordTrace tailWord_1346550 prefixEnd_1346550 153650527847069300140519 := by
  unfold tailWord_1346550
  simp only [CollatzResearch.WordTrace]
  refine ⟨3069544579480424829754319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32741808847791198184046069 3069544579480424829754319)
  ·
    refine ⟨4604316869220637244631479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3069544579480424829754319 4604316869220637244631479)
    ·
      refine ⟨6906475303830955866947219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4604316869220637244631479 6906475303830955866947219)
      ·
        refine ⟨10359712955746433800420829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6906475303830955866947219 10359712955746433800420829)
        ·
          refine ⟨3884892358404912675157811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10359712955746433800420829 3884892358404912675157811)
          ·
            refine ⟨5827338537607369012736717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3884892358404912675157811 5827338537607369012736717)
            ·
              refine ⟨2185251951602763379776269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5827338537607369012736717 2185251951602763379776269)
              ·
                refine ⟨819469481851036267416101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2185251951602763379776269 819469481851036267416101)
                ·
                  refine ⟨153650527847069300140519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 819469481851036267416101 153650527847069300140519)
                  ·
                    rfl

theorem cell22_1346550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_1346550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1346550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1346550 prefixEnd_1346550 := by exact prefixLift 1346550
  have htrace : WordTrace (prefixWord ++ tailWord_1346550) baseStart_1346550 baseEnd_1346550 := by
    simpa [prefixWord, tailWord_1346550, baseEnd_1346550] using wordTrace_append hprefix tailTrace_1346550
  have hstable : (prefixWord ++ tailWord_1346550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346550).length < 2 ^ (prefixWord ++ tailWord_1346550).sum := by decide
  have hdescent : baseEnd_1346550 < baseStart_1346550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346561 : List Nat := [1, 2, 4, 1, 2, 4, 8]
def baseStart_1346561 : Nat := 118140960795 + 1346561 * 2 ^ 59
def prefixEnd_1346561 : Nat := 4983230072969 + 3 ^ 40 * 1346561 * 2
def baseEnd_1346561 : Nat := 17072420335778056977649

theorem tailTrace_1346561 : CollatzResearch.WordTrace tailWord_1346561 prefixEnd_1346561 17072420335778056977649 := by
  unfold tailWord_1346561
  simp only [CollatzResearch.WordTrace]
  refine ⟨49113114474646946154719537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32742076316431297436479691 49113114474646946154719537)
  ·
    refine ⟨36834835855985209616039653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49113114474646946154719537 36834835855985209616039653)
    ·
      refine ⟨6906531722997226803007435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36834835855985209616039653 6906531722997226803007435)
      ·
        refine ⟨10359797584495840204511153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6906531722997226803007435 10359797584495840204511153)
        ·
          refine ⟨7769848188371880153383365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10359797584495840204511153 7769848188371880153383365)
          ·
            refine ⟨1456846535319727528759381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7769848188371880153383365 1456846535319727528759381)
            ·
              refine ⟨17072420335778056977649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1456846535319727528759381 17072420335778056977649)
              ·
                rfl

theorem cell22_1346561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 8].length) (baseStart_1346561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1346561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1346561 prefixEnd_1346561 := by exact prefixLift 1346561
  have htrace : WordTrace (prefixWord ++ tailWord_1346561) baseStart_1346561 baseEnd_1346561 := by
    simpa [prefixWord, tailWord_1346561, baseEnd_1346561] using wordTrace_append hprefix tailTrace_1346561
  have hstable : (prefixWord ++ tailWord_1346561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346561).length < 2 ^ (prefixWord ++ tailWord_1346561).sum := by decide
  have hdescent : baseEnd_1346561 < baseStart_1346561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346610 : List Nat := [3, 2, 1, 1, 2, 2, 2, 5, 1, 3]
def baseStart_1346610 : Nat := 118140960795 + 1346610 * 2 ^ 59
def prefixEnd_1346610 : Nat := 4983230072969 + 3 ^ 40 * 1346610 * 2
def baseEnd_1346610 : Nat := 460972122767387743921373

theorem tailTrace_1346610 : CollatzResearch.WordTrace tailWord_1346610 prefixEnd_1346610 460972122767387743921373 := by
  unfold tailWord_1346610
  simp only [CollatzResearch.WordTrace]
  refine ⟨12278725412867356880813321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32743267767646285015502189 12278725412867356880813321)
  ·
    refine ⟨9209044059650517660609991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12278725412867356880813321 9209044059650517660609991)
    ·
      refine ⟨13813566089475776490914987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9209044059650517660609991 13813566089475776490914987)
      ·
        refine ⟨20720349134213664736372481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13813566089475776490914987 20720349134213664736372481)
        ·
          refine ⟨15540261850660248552279361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20720349134213664736372481 15540261850660248552279361)
          ·
            refine ⟨11655196387995186414209521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15540261850660248552279361 11655196387995186414209521)
            ·
              refine ⟨8741397290996389810657141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11655196387995186414209521 8741397290996389810657141)
              ·
                refine ⟨819505996030911544749107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8741397290996389810657141 819505996030911544749107)
                ·
                  refine ⟨1229258994046367317123661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 819505996030911544749107 1229258994046367317123661)
                  ·
                    refine ⟨460972122767387743921373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1229258994046367317123661 460972122767387743921373)
                    ·
                      rfl

theorem cell22_1346610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 5, 1, 3].length) (baseStart_1346610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1346610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1346610 prefixEnd_1346610 := by exact prefixLift 1346610
  have htrace : WordTrace (prefixWord ++ tailWord_1346610) baseStart_1346610 baseEnd_1346610 := by
    simpa [prefixWord, tailWord_1346610, baseEnd_1346610] using wordTrace_append hprefix tailTrace_1346610
  have hstable : (prefixWord ++ tailWord_1346610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346610).length < 2 ^ (prefixWord ++ tailWord_1346610).sum := by decide
  have hdescent : baseEnd_1346610 < baseStart_1346610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346670 : List Nat := [4, 1, 2, 2, 1, 3, 1, 3, 1, 4]
def baseStart_1346670 : Nat := 118140960795 + 1346670 * 2 ^ 59
def prefixEnd_1346670 : Nat := 4983230072969 + 3 ^ 40 * 1346670 * 2
def baseEnd_1346670 : Nat := 460992661993567587421189

theorem tailTrace_1346670 : CollatzResearch.WordTrace tailWord_1346670 prefixEnd_1346670 460992661993567587421189 := by
  unfold tailWord_1346670
  simp only [CollatzResearch.WordTrace]
  refine ⟨6139636253906507221304683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32744726687501371846958309 6139636253906507221304683)
  ·
    refine ⟨9209454380859760831957025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6139636253906507221304683 9209454380859760831957025)
    ·
      refine ⟨6907090785644820623967769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9209454380859760831957025 6907090785644820623967769)
      ·
        refine ⟨5180318089233615467975827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6907090785644820623967769 5180318089233615467975827)
        ·
          refine ⟨7770477133850423201963741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5180318089233615467975827 7770477133850423201963741)
          ·
            refine ⟨2913928925193908700736403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7770477133850423201963741 2913928925193908700736403)
            ·
              refine ⟨4370893387790863051104605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2913928925193908700736403 4370893387790863051104605)
              ·
                refine ⟨1639085020421573644164227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4370893387790863051104605 1639085020421573644164227)
                ·
                  refine ⟨2458627530632360466246341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1639085020421573644164227 2458627530632360466246341)
                  ·
                    refine ⟨460992661993567587421189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2458627530632360466246341 460992661993567587421189)
                    ·
                      rfl

theorem cell22_1346670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_1346670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1346670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1346670 prefixEnd_1346670 := by exact prefixLift 1346670
  have htrace : WordTrace (prefixWord ++ tailWord_1346670) baseStart_1346670 baseEnd_1346670 := by
    simpa [prefixWord, tailWord_1346670, baseEnd_1346670] using wordTrace_append hprefix tailTrace_1346670
  have hstable : (prefixWord ++ tailWord_1346670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346670).length < 2 ^ (prefixWord ++ tailWord_1346670).sum := by decide
  have hdescent : baseEnd_1346670 < baseStart_1346670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346719 : List Nat := [1, 1, 2, 6, 3, 1, 1, 3, 4]
def baseStart_1346719 : Nat := 118140960795 + 1346719 * 2 ^ 59
def prefixEnd_1346719 : Nat := 4983230072969 + 3 ^ 40 * 1346719 * 2
def baseEnd_1346719 : Nat := 153669811898315930982013

theorem tailTrace_1346719 : CollatzResearch.WordTrace tailWord_1346719 prefixEnd_1346719 153669811898315930982013 := by
  unfold tailWord_1346719
  simp only [CollatzResearch.WordTrace]
  refine ⟨49118877208074539138971211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32745918138716359425980807 49118877208074539138971211)
  ·
    refine ⟨73678315812111808708456817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49118877208074539138971211 73678315812111808708456817)
    ·
      refine ⟨55258736859083856531342613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73678315812111808708456817 55258736859083856531342613)
      ·
        refine ⟨2590253290269555774906685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 55258736859083856531342613 2590253290269555774906685)
        ·
          refine ⟨971344983851083415590007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2590253290269555774906685 971344983851083415590007)
          ·
            refine ⟨1457017475776625123385011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 971344983851083415590007 1457017475776625123385011)
            ·
              refine ⟨2185526213664937685077517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1457017475776625123385011 2185526213664937685077517)
              ·
                refine ⟨819572330124351631904069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2185526213664937685077517 819572330124351631904069)
                ·
                  refine ⟨153669811898315930982013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 819572330124351631904069 153669811898315930982013)
                  ·
                    rfl

theorem cell22_1346719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 3, 4].length) (baseStart_1346719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1346719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1346719 prefixEnd_1346719 := by exact prefixLift 1346719
  have htrace : WordTrace (prefixWord ++ tailWord_1346719) baseStart_1346719 baseEnd_1346719 := by
    simpa [prefixWord, tailWord_1346719, baseEnd_1346719] using wordTrace_append hprefix tailTrace_1346719
  have hstable : (prefixWord ++ tailWord_1346719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346719).length < 2 ^ (prefixWord ++ tailWord_1346719).sum := by decide
  have hdescent : baseEnd_1346719 < baseStart_1346719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346730 : List Nat := [3, 1, 5, 1, 1, 3, 8]
def baseStart_1346730 : Nat := 118140960795 + 1346730 * 2 ^ 59
def prefixEnd_1346730 : Nat := 4983230072969 + 3 ^ 40 * 1346730 * 2
def baseEnd_1346730 : Nat := 17074563008138793737815

theorem tailTrace_1346730 : CollatzResearch.WordTrace tailWord_1346730 prefixEnd_1346730 17074563008138793737815 := by
  unfold tailWord_1346730
  simp only [CollatzResearch.WordTrace]
  refine ⟨12279819602758672004405411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32746185607356458678414429 12279819602758672004405411)
  ·
    refine ⟨18419729404138008006608117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12279819602758672004405411 18419729404138008006608117)
    ·
      refine ⟨1726849631637938250619511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18419729404138008006608117 1726849631637938250619511)
      ·
        refine ⟨2590274447456907375929267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1726849631637938250619511 2590274447456907375929267)
        ·
          refine ⟨3885411671185361063893901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2590274447456907375929267 3885411671185361063893901)
          ·
            refine ⟨1457029376694510398960213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3885411671185361063893901 1457029376694510398960213)
            ·
              refine ⟨17074563008138793737815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1457029376694510398960213 17074563008138793737815)
              ·
                rfl

theorem cell22_1346730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 8].length) (baseStart_1346730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1346730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1346730 prefixEnd_1346730 := by exact prefixLift 1346730
  have htrace : WordTrace (prefixWord ++ tailWord_1346730) baseStart_1346730 baseEnd_1346730 := by
    simpa [prefixWord, tailWord_1346730, baseEnd_1346730] using wordTrace_append hprefix tailTrace_1346730
  have hstable : (prefixWord ++ tailWord_1346730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346730).length < 2 ^ (prefixWord ++ tailWord_1346730).sum := by decide
  have hdescent : baseEnd_1346730 < baseStart_1346730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346745 : List Nat := [1, 2, 1, 4, 1, 3, 3, 1, 3, 3]
def baseStart_1346745 : Nat := 118140960795 + 1346745 * 2 ^ 59
def prefixEnd_1346745 : Nat := 4983230072969 + 3 ^ 40 * 1346745 * 2
def baseEnd_1346745 : Nat := 461018336026292391795959

theorem tailTrace_1346745 : CollatzResearch.WordTrace tailWord_1346745 prefixEnd_1346745 461018336026292391795959 := by
  unfold tailWord_1346745
  simp only [CollatzResearch.WordTrace]
  refine ⟨49119825505980345579417689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32746550337320230386278459 49119825505980345579417689)
  ·
    refine ⟨36839869129485259184563267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49119825505980345579417689 36839869129485259184563267)
    ·
      refine ⟨55259803694227888776844901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36839869129485259184563267 55259803694227888776844901)
      ·
        refine ⟨10361213192667729145658419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55259803694227888776844901 10361213192667729145658419)
        ·
          refine ⟨15541819789001593718487629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10361213192667729145658419 15541819789001593718487629)
          ·
            refine ⟨5828182420875597644432861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15541819789001593718487629 5828182420875597644432861)
            ·
              refine ⟨2185568407828349116662323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5828182420875597644432861 2185568407828349116662323)
              ·
                refine ⟨3278352611742523674993485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2185568407828349116662323 3278352611742523674993485)
                ·
                  refine ⟨1229382229403446378122557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3278352611742523674993485 1229382229403446378122557)
                  ·
                    refine ⟨461018336026292391795959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1229382229403446378122557 461018336026292391795959)
                    ·
                      rfl

theorem cell22_1346745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 1, 3, 3].length) (baseStart_1346745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1346745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1346745 prefixEnd_1346745 := by exact prefixLift 1346745
  have htrace : WordTrace (prefixWord ++ tailWord_1346745) baseStart_1346745 baseEnd_1346745 := by
    simpa [prefixWord, tailWord_1346745, baseEnd_1346745] using wordTrace_append hprefix tailTrace_1346745
  have hstable : (prefixWord ++ tailWord_1346745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346745).length < 2 ^ (prefixWord ++ tailWord_1346745).sum := by decide
  have hdescent : baseEnd_1346745 < baseStart_1346745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346771 : List Nat := [1, 1, 1, 2, 1, 1, 1, 4, 2, 8]
def baseStart_1346771 : Nat := 118140960795 + 1346771 * 2 ^ 59
def prefixEnd_1346771 : Nat := 4983230072969 + 3 ^ 40 * 1346771 * 2
def baseEnd_1346771 : Nat := 461027236357636990645879

theorem tailTrace_1346771 : CollatzResearch.WordTrace tailWord_1346771 prefixEnd_1346771 461027236357636990645879 := by
  unfold tailWord_1346771
  simp only [CollatzResearch.WordTrace]
  refine ⟨49120773803886152019864167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32747182535924101346576111 49120773803886152019864167)
  ·
    refine ⟨73681160705829228029796251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49120773803886152019864167 73681160705829228029796251)
    ·
      refine ⟨110521741058743842044694377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73681160705829228029796251 110521741058743842044694377)
      ·
        refine ⟨82891305794057881533520783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110521741058743842044694377 82891305794057881533520783)
        ·
          refine ⟨124336958691086822300281175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82891305794057881533520783 124336958691086822300281175)
          ·
            refine ⟨186505438036630233450421763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124336958691086822300281175 186505438036630233450421763)
            ·
              refine ⟨279758157054945350175632645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186505438036630233450421763 279758157054945350175632645)
              ·
                refine ⟨52454654447802253157931121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 279758157054945350175632645 52454654447802253157931121)
                ·
                  refine ⟨39340990835851689868448341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52454654447802253157931121 39340990835851689868448341)
                  ·
                    refine ⟨461027236357636990645879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 39340990835851689868448341 461027236357636990645879)
                    ·
                      rfl

theorem cell22_1346771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 8].length) (baseStart_1346771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1346771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1346771 prefixEnd_1346771 := by exact prefixLift 1346771
  have htrace : WordTrace (prefixWord ++ tailWord_1346771) baseStart_1346771 baseEnd_1346771 := by
    simpa [prefixWord, tailWord_1346771, baseEnd_1346771] using wordTrace_append hprefix tailTrace_1346771
  have hstable : (prefixWord ++ tailWord_1346771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346771).length < 2 ^ (prefixWord ++ tailWord_1346771).sum := by decide
  have hdescent : baseEnd_1346771 < baseStart_1346771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346820 : List Nat := [2, 3, 2, 2, 2, 2, 1, 2, 6]
def baseStart_1346820 : Nat := 118140960795 + 1346820 * 2 ^ 59
def prefixEnd_1346820 : Nat := 4983230072969 + 3 ^ 40 * 1346820 * 2
def baseEnd_1346820 : Nat := 153681336686339065390243

theorem tailTrace_1346820 : CollatzResearch.WordTrace tailWord_1346820 prefixEnd_1346820 153681336686339065390243 := by
  unfold tailWord_1346820
  simp only [CollatzResearch.WordTrace]
  refine ⟨24561280490354316694198957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32748373987139088925598609 24561280490354316694198957)
  ·
    refine ⟨9210480183882868760324609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24561280490354316694198957 9210480183882868760324609)
    ·
      refine ⟨6907860137912151570243457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9210480183882868760324609 6907860137912151570243457)
      ·
        refine ⟨5180895103434113677682593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6907860137912151570243457 5180895103434113677682593)
        ·
          refine ⟨3885671327575585258261945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5180895103434113677682593 3885671327575585258261945)
          ·
            refine ⟨2914253495681688943696459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3885671327575585258261945 2914253495681688943696459)
            ·
              refine ⟨4371380243522533415544689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2914253495681688943696459 4371380243522533415544689)
              ·
                refine ⟨3278535182641900061658517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4371380243522533415544689 3278535182641900061658517)
                ·
                  refine ⟨153681336686339065390243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3278535182641900061658517 153681336686339065390243)
                  ·
                    rfl

theorem cell22_1346820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 2, 6].length) (baseStart_1346820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1346820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1346820 prefixEnd_1346820 := by exact prefixLift 1346820
  have htrace : WordTrace (prefixWord ++ tailWord_1346820) baseStart_1346820 baseEnd_1346820 := by
    simpa [prefixWord, tailWord_1346820, baseEnd_1346820] using wordTrace_append hprefix tailTrace_1346820
  have hstable : (prefixWord ++ tailWord_1346820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346820).length < 2 ^ (prefixWord ++ tailWord_1346820).sum := by decide
  have hdescent : baseEnd_1346820 < baseStart_1346820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346833 : List Nat := [1, 2, 2, 1, 1, 4, 3, 1, 1, 6]
def baseStart_1346833 : Nat := 118140960795 + 1346833 * 2 ^ 59
def prefixEnd_1346833 : Nat := 4983230072969 + 3 ^ 40 * 1346833 * 2
def baseEnd_1346833 : Nat := 461048460224689495595689

theorem tailTrace_1346833 : CollatzResearch.WordTrace tailWord_1346833 prefixEnd_1346833 461048460224689495595689 := by
  unfold tailWord_1346833
  simp only [CollatzResearch.WordTrace]
  refine ⟨49123035129661536608621153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32748690086441024405747435 49123035129661536608621153)
  ·
    refine ⟨36842276347246152456465865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49123035129661536608621153 36842276347246152456465865)
    ·
      refine ⟨27631707260434614342349399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36842276347246152456465865 27631707260434614342349399)
      ·
        refine ⟨41447560890651921513524099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27631707260434614342349399 41447560890651921513524099)
        ·
          refine ⟨62171341335977882270286149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41447560890651921513524099 62171341335977882270286149)
          ·
            refine ⟨11657126500495852925678653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62171341335977882270286149 11657126500495852925678653)
            ·
              refine ⟨4371422437685944847129495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11657126500495852925678653 4371422437685944847129495)
              ·
                refine ⟨6557133656528917270694243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4371422437685944847129495 6557133656528917270694243)
                ·
                  refine ⟨9835700484793375906041365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6557133656528917270694243 9835700484793375906041365)
                  ·
                    refine ⟨461048460224689495595689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9835700484793375906041365 461048460224689495595689)
                    ·
                      rfl

theorem cell22_1346833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 6].length) (baseStart_1346833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1346833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1346833 prefixEnd_1346833 := by exact prefixLift 1346833
  have htrace : WordTrace (prefixWord ++ tailWord_1346833) baseStart_1346833 baseEnd_1346833 := by
    simpa [prefixWord, tailWord_1346833, baseEnd_1346833] using wordTrace_append hprefix tailTrace_1346833
  have hstable : (prefixWord ++ tailWord_1346833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346833).length < 2 ^ (prefixWord ++ tailWord_1346833).sum := by decide
  have hdescent : baseEnd_1346833 < baseStart_1346833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346869 : List Nat := [1, 3, 3, 1, 2, 3, 3, 1, 2, 3]
def baseStart_1346869 : Nat := 118140960795 + 1346869 * 2 ^ 59
def prefixEnd_1346869 : Nat := 4983230072969 + 3 ^ 40 * 1346869 * 2
def baseEnd_1346869 : Nat := 461060783760397401695579

theorem tailTrace_1346869 : CollatzResearch.WordTrace tailWord_1346869 prefixEnd_1346869 461060783760397401695579 := by
  unfold tailWord_1346869
  simp only [CollatzResearch.WordTrace]
  refine ⟨49124348157531114756931661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32749565438354076504621107 49124348157531114756931661)
  ·
    refine ⟨18421630559074168033849373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49124348157531114756931661 18421630559074168033849373)
    ·
      refine ⟨6908111459652813012693515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18421630559074168033849373 6908111459652813012693515)
      ·
        refine ⟨10362167189479219519040273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6908111459652813012693515 10362167189479219519040273)
        ·
          refine ⟨7771625392109414639280205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10362167189479219519040273 7771625392109414639280205)
          ·
            refine ⟨2914359522041030489730077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7771625392109414639280205 2914359522041030489730077)
            ·
              refine ⟨1092884820765386433648779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2914359522041030489730077 1092884820765386433648779)
              ·
                refine ⟨1639327231148079650473169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1092884820765386433648779 1639327231148079650473169)
                ·
                  refine ⟨1229495423361059737854877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1639327231148079650473169 1229495423361059737854877)
                  ·
                    refine ⟨461060783760397401695579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1229495423361059737854877 461060783760397401695579)
                    ·
                      rfl

theorem cell22_1346869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3, 1, 2, 3].length) (baseStart_1346869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1346869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1346869 prefixEnd_1346869 := by exact prefixLift 1346869
  have htrace : WordTrace (prefixWord ++ tailWord_1346869) baseStart_1346869 baseEnd_1346869 := by
    simpa [prefixWord, tailWord_1346869, baseEnd_1346869] using wordTrace_append hprefix tailTrace_1346869
  have hstable : (prefixWord ++ tailWord_1346869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346869).length < 2 ^ (prefixWord ++ tailWord_1346869).sum := by decide
  have hdescent : baseEnd_1346869 < baseStart_1346869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346880 : List Nat := [2, 1, 1, 2, 2, 1, 3, 4, 3, 3]
def baseStart_1346880 : Nat := 118140960795 + 1346880 * 2 ^ 59
def prefixEnd_1346880 : Nat := 4983230072969 + 3 ^ 40 * 1346880 * 2
def baseEnd_1346880 : Nat := 461064549285197039670545

theorem tailTrace_1346880 : CollatzResearch.WordTrace tailWord_1346880 prefixEnd_1346880 461064549285197039670545 := by
  unfold tailWord_1346880
  simp only [CollatzResearch.WordTrace]
  refine ⟨24562374680245631817791047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32749832906994175757054729 24562374680245631817791047)
  ·
    refine ⟨36843562020368447726686571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24562374680245631817791047 36843562020368447726686571)
    ·
      refine ⟨55265343030552671590029857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36843562020368447726686571 55265343030552671590029857)
      ·
        refine ⟨41449007272914503692522393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55265343030552671590029857 41449007272914503692522393)
        ·
          refine ⟨31086755454685877769391795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41449007272914503692522393 31086755454685877769391795)
          ·
            refine ⟨46630133182028816654087693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31086755454685877769391795 46630133182028816654087693)
            ·
              refine ⟨17486299943260806245282885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46630133182028816654087693 17486299943260806245282885)
              ·
                refine ⟨3278681239361401170990541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17486299943260806245282885 3278681239361401170990541)
                ·
                  refine ⟨1229505464760525439121453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3278681239361401170990541 1229505464760525439121453)
                  ·
                    refine ⟨461064549285197039670545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1229505464760525439121453 461064549285197039670545)
                    ·
                      rfl

theorem cell22_1346880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4, 3, 3].length) (baseStart_1346880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1346880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1346880 prefixEnd_1346880 := by exact prefixLift 1346880
  have htrace : WordTrace (prefixWord ++ tailWord_1346880) baseStart_1346880 baseEnd_1346880 := by
    simpa [prefixWord, tailWord_1346880, baseEnd_1346880] using wordTrace_append hprefix tailTrace_1346880
  have hstable : (prefixWord ++ tailWord_1346880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346880).length < 2 ^ (prefixWord ++ tailWord_1346880).sum := by decide
  have hdescent : baseEnd_1346880 < baseStart_1346880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346940 : List Nat := [2, 2, 2, 1, 1, 1, 5, 1, 3, 4]
def baseStart_1346940 : Nat := 118140960795 + 1346940 * 2 ^ 59
def prefixEnd_1346940 : Nat := 4983230072969 + 3 ^ 40 * 1346940 * 2
def baseEnd_1346940 : Nat := 461085088511376883170361

theorem tailTrace_1346940 : CollatzResearch.WordTrace tailWord_1346940 prefixEnd_1346940 461085088511376883170361 := by
  unfold tailWord_1346940
  simp only [CollatzResearch.WordTrace]
  refine ⟨24563468870136946941383137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32751291826849262588510849 24563468870136946941383137)
  ·
    refine ⟨18422601652602710206037353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24563468870136946941383137 18422601652602710206037353)
    ·
      refine ⟨13816951239452032654528015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18422601652602710206037353 13816951239452032654528015)
      ·
        refine ⟨20725426859178048981792023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13816951239452032654528015 20725426859178048981792023)
        ·
          refine ⟨31088140288767073472688035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20725426859178048981792023 31088140288767073472688035)
          ·
            refine ⟨46632210433150610209032053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31088140288767073472688035 46632210433150610209032053)
            ·
              refine ⟨4371769728107869707096755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46632210433150610209032053 4371769728107869707096755)
              ·
                refine ⟨6557654592161804560645133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4371769728107869707096755 6557654592161804560645133)
                ·
                  refine ⟨2459120472060676710241925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6557654592161804560645133 2459120472060676710241925)
                  ·
                    refine ⟨461085088511376883170361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2459120472060676710241925 461085088511376883170361)
                    ·
                      rfl

theorem cell22_1346940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_1346940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1346940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1346940 prefixEnd_1346940 := by exact prefixLift 1346940
  have htrace : WordTrace (prefixWord ++ tailWord_1346940) baseStart_1346940 baseEnd_1346940 := by
    simpa [prefixWord, tailWord_1346940, baseEnd_1346940] using wordTrace_append hprefix tailTrace_1346940
  have hstable : (prefixWord ++ tailWord_1346940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346940).length < 2 ^ (prefixWord ++ tailWord_1346940).sum := by decide
  have hdescent : baseEnd_1346940 < baseStart_1346940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346970 : List Nat := [3, 1, 1, 4, 1, 1, 1, 2, 3, 5]
def baseStart_1346970 : Nat := 118140960795 + 1346970 * 2 ^ 59
def prefixEnd_1346970 : Nat := 4983230072969 + 3 ^ 40 * 1346970 * 2
def baseEnd_1346970 : Nat := 461095358124466804920269

theorem tailTrace_1346970 : CollatzResearch.WordTrace tailWord_1346970 prefixEnd_1346970 461095358124466804920269 := by
  unfold tailWord_1346970
  simp only [CollatzResearch.WordTrace]
  refine ⟨12282007982541302251589591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32752021286776806004238909 12282007982541302251589591)
  ·
    refine ⟨18423011973811953377384387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12282007982541302251589591 18423011973811953377384387)
    ·
      refine ⟨27634517960717930066076581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18423011973811953377384387 27634517960717930066076581)
      ·
        refine ⟨5181472117634611887389359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27634517960717930066076581 5181472117634611887389359)
        ·
          refine ⟨7772208176451917831084039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5181472117634611887389359 7772208176451917831084039)
          ·
            refine ⟨11658312264677876746626059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7772208176451917831084039 11658312264677876746626059)
            ·
              refine ⟨17487468397016815119939089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11658312264677876746626059 17487468397016815119939089)
              ·
                refine ⟨13115601297762611339954317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17487468397016815119939089 13115601297762611339954317)
                ·
                  refine ⟨4918350486660979252482869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13115601297762611339954317 4918350486660979252482869)
                  ·
                    refine ⟨461095358124466804920269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4918350486660979252482869 461095358124466804920269)
                    ·
                      rfl

theorem cell22_1346970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 3, 5].length) (baseStart_1346970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1346970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1346970 prefixEnd_1346970 := by exact prefixLift 1346970
  have htrace : WordTrace (prefixWord ++ tailWord_1346970) baseStart_1346970 baseEnd_1346970 := by
    simpa [prefixWord, tailWord_1346970, baseEnd_1346970] using wordTrace_append hprefix tailTrace_1346970
  have hstable : (prefixWord ++ tailWord_1346970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346970).length < 2 ^ (prefixWord ++ tailWord_1346970).sum := by decide
  have hdescent : baseEnd_1346970 < baseStart_1346970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347032 : List Nat := [2, 1, 2, 2, 2, 1, 3, 3, 3, 3]
def baseStart_1347032 : Nat := 118140960795 + 1347032 * 2 ^ 59
def prefixEnd_1347032 : Nat := 4983230072969 + 3 ^ 40 * 1347032 * 2
def baseEnd_1347032 : Nat := 461116581991519309870079

theorem tailTrace_1347032 : CollatzResearch.WordTrace tailWord_1347032 prefixEnd_1347032 461116581991519309870079 := by
  unfold tailWord_1347032
  simp only [CollatzResearch.WordTrace]
  refine ⟨24565146627970296797557675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32753528837293729063410233 24565146627970296797557675)
  ·
    refine ⟨36847719941955445196336513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24565146627970296797557675 36847719941955445196336513)
    ·
      refine ⟨27635789956466583897252385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36847719941955445196336513 27635789956466583897252385)
      ·
        refine ⟨20726842467349937922939289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27635789956466583897252385 20726842467349937922939289)
        ·
          refine ⟨15545131850512453442204467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20726842467349937922939289 15545131850512453442204467)
          ·
            refine ⟨23317697775768680163306701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15545131850512453442204467 23317697775768680163306701)
            ·
              refine ⟨8744136665913255061240013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23317697775768680163306701 8744136665913255061240013)
              ·
                refine ⟨3279051249717470647965005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8744136665913255061240013 3279051249717470647965005)
                ·
                  refine ⟨1229644218644051492986877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3279051249717470647965005 1229644218644051492986877)
                  ·
                    refine ⟨461116581991519309870079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1229644218644051492986877 461116581991519309870079)
                    ·
                      rfl

theorem cell22_1347032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3, 3, 3].length) (baseStart_1347032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1347032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1347032 prefixEnd_1347032 := by exact prefixLift 1347032
  have htrace : WordTrace (prefixWord ++ tailWord_1347032) baseStart_1347032 baseEnd_1347032 := by
    simpa [prefixWord, tailWord_1347032, baseEnd_1347032] using wordTrace_append hprefix tailTrace_1347032
  have hstable : (prefixWord ++ tailWord_1347032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347032).length < 2 ^ (prefixWord ++ tailWord_1347032).sum := by decide
  have hdescent : baseEnd_1347032 < baseStart_1347032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347062 : List Nat := [5, 1, 1, 1, 2, 2, 1, 2, 7]
def baseStart_1347062 : Nat := 118140960795 + 1347062 * 2 ^ 59
def prefixEnd_1347062 : Nat := 4983230072969 + 3 ^ 40 * 1347062 * 2
def baseEnd_1347062 : Nat := 153708950534869743873329

theorem tailTrace_1347062 : CollatzResearch.WordTrace tailWord_1347062 prefixEnd_1347062 153708950534869743873329 := by
  unfold tailWord_1347062
  simp only [CollatzResearch.WordTrace]
  refine ⟨3070711715364494294919215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32754258297221272479138293 3070711715364494294919215)
  ·
    refine ⟨4606067573046741442378823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3070711715364494294919215 4606067573046741442378823)
    ·
      refine ⟨6909101359570112163568235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4606067573046741442378823 6909101359570112163568235)
      ·
        refine ⟨10363652039355168245352353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6909101359570112163568235 10363652039355168245352353)
        ·
          refine ⟨7772739029516376184014265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10363652039355168245352353 7772739029516376184014265)
          ·
            refine ⟨5829554272137282138010699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7772739029516376184014265 5829554272137282138010699)
            ·
              refine ⟨8744331408205923207016049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5829554272137282138010699 8744331408205923207016049)
              ·
                refine ⟨6558248556154442405262037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8744331408205923207016049 6558248556154442405262037)
                ·
                  refine ⟨153708950534869743873329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6558248556154442405262037 153708950534869743873329)
                  ·
                    rfl

theorem cell22_1347062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_1347062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1347062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1347062 prefixEnd_1347062 := by exact prefixLift 1347062
  have htrace : WordTrace (prefixWord ++ tailWord_1347062) baseStart_1347062 baseEnd_1347062 := by
    simpa [prefixWord, tailWord_1347062, baseEnd_1347062] using wordTrace_append hprefix tailTrace_1347062
  have hstable : (prefixWord ++ tailWord_1347062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347062).length < 2 ^ (prefixWord ++ tailWord_1347062).sum := by decide
  have hdescent : baseEnd_1347062 < baseStart_1347062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347083 : List Nat := [1, 1, 1, 1, 8, 1, 3, 2, 1, 3]
def baseStart_1347083 : Nat := 118140960795 + 1347083 * 2 ^ 59
def prefixEnd_1347083 : Nat := 4983230072969 + 3 ^ 40 * 1347083 * 2
def baseEnd_1347083 : Nat := 461134040333772176844923

theorem tailTrace_1347083 : CollatzResearch.WordTrace tailWord_1347083 prefixEnd_1347083 461134040333772176844923 := by
  unfold tailWord_1347083
  simp only [CollatzResearch.WordTrace]
  refine ⟨49132153378755829305221903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32754768919170552870147935 49132153378755829305221903)
  ·
    refine ⟨73698230068133743957832855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49132153378755829305221903 73698230068133743957832855)
    ·
      refine ⟨110547345102200615936749283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73698230068133743957832855 110547345102200615936749283)
      ·
        refine ⟨165821017653300923905123925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110547345102200615936749283 165821017653300923905123925)
        ·
          refine ⟨1943215050624620202013171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 165821017653300923905123925 1943215050624620202013171)
          ·
            refine ⟨2914822575936930303019757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1943215050624620202013171 2914822575936930303019757)
            ·
              refine ⟨1093058465976348863632409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2914822575936930303019757 1093058465976348863632409)
              ·
                refine ⟨819793849482261647724307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1093058465976348863632409 819793849482261647724307)
                ·
                  refine ⟨1229690774223392471586461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 819793849482261647724307 1229690774223392471586461)
                  ·
                    refine ⟨461134040333772176844923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1229690774223392471586461 461134040333772176844923)
                    ·
                      rfl

theorem cell22_1347083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3, 2, 1, 3].length) (baseStart_1347083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1347083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1347083 prefixEnd_1347083 := by exact prefixLift 1347083
  have htrace : WordTrace (prefixWord ++ tailWord_1347083) baseStart_1347083 baseEnd_1347083 := by
    simpa [prefixWord, tailWord_1347083, baseEnd_1347083] using wordTrace_append hprefix tailTrace_1347083
  have hstable : (prefixWord ++ tailWord_1347083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347083).length < 2 ^ (prefixWord ++ tailWord_1347083).sum := by decide
  have hdescent : baseEnd_1347083 < baseStart_1347083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347096 : List Nat := [2, 1, 2, 3, 4, 2, 2, 1, 5]
def baseStart_1347096 : Nat := 118140960795 + 1347096 * 2 ^ 59
def prefixEnd_1347096 : Nat := 4983230072969 + 3 ^ 40 * 1347096 * 2
def baseEnd_1347096 : Nat := 153712830166481492089961

theorem tailTrace_1347096 : CollatzResearch.WordTrace tailWord_1347096 prefixEnd_1347096 153712830166481492089961 := by
  unfold tailWord_1347096
  simp only [CollatzResearch.WordTrace]
  refine ⟨24566313763854366262722571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32755085018472488350296761 24566313763854366262722571)
  ·
    refine ⟨36849470645781549394083857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24566313763854366262722571 36849470645781549394083857)
    ·
      refine ⟨27637102984336162045562893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36849470645781549394083857 27637102984336162045562893)
      ·
        refine ⟨10363913619126060767086085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27637102984336162045562893 10363913619126060767086085)
        ·
          refine ⟨1943233803586136393828641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10363913619126060767086085 1943233803586136393828641)
          ·
            refine ⟨1457425352689602295371481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1943233803586136393828641 1457425352689602295371481)
            ·
              refine ⟨1093069014517201721528611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1457425352689602295371481 1093069014517201721528611)
              ·
                refine ⟨1639603521775802582292917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1093069014517201721528611 1639603521775802582292917)
                ·
                  refine ⟨153712830166481492089961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1639603521775802582292917 153712830166481492089961)
                  ·
                    rfl

theorem cell22_1347096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2, 1, 5].length) (baseStart_1347096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1347096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1347096 prefixEnd_1347096 := by exact prefixLift 1347096
  have htrace : WordTrace (prefixWord ++ tailWord_1347096) baseStart_1347096 baseEnd_1347096 := by
    simpa [prefixWord, tailWord_1347096, baseEnd_1347096] using wordTrace_append hprefix tailTrace_1347096
  have hstable : (prefixWord ++ tailWord_1347096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347096).length < 2 ^ (prefixWord ++ tailWord_1347096).sum := by decide
  have hdescent : baseEnd_1347096 < baseStart_1347096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347135 : List Nat := [1, 1, 2, 2, 3, 13]
def baseStart_1347135 : Nat := 118140960795 + 1347135 * 2 ^ 59
def prefixEnd_1347135 : Nat := 4983230072969 + 3 ^ 40 * 1347135 * 2
def baseEnd_1347135 : Nat := 5693232604894584870923

theorem tailTrace_1347135 : CollatzResearch.WordTrace tailWord_1347135 prefixEnd_1347135 5693232604894584870923 := by
  unfold tailWord_1347135
  simp only [CollatzResearch.WordTrace]
  refine ⟨49134049974567442186114859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32756033316378294790743239 49134049974567442186114859)
  ·
    refine ⟨73701074961851163279172289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49134049974567442186114859 73701074961851163279172289)
    ·
      refine ⟨55275806221388372459379217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73701074961851163279172289 55275806221388372459379217)
      ·
        refine ⟨41456854666041279344534413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55275806221388372459379217 41456854666041279344534413)
        ·
          refine ⟨15546320499765479754200405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41456854666041279344534413 15546320499765479754200405)
          ·
            refine ⟨5693232604894584870923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 15546320499765479754200405 5693232604894584870923)
            ·
              rfl

theorem cell22_1347135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 13].length) (baseStart_1347135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1347135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1347135 prefixEnd_1347135 := by exact prefixLift 1347135
  have htrace : WordTrace (prefixWord ++ tailWord_1347135) baseStart_1347135 baseEnd_1347135 := by
    simpa [prefixWord, tailWord_1347135, baseEnd_1347135] using wordTrace_append hprefix tailTrace_1347135
  have hstable : (prefixWord ++ tailWord_1347135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347135).length < 2 ^ (prefixWord ++ tailWord_1347135).sum := by decide
  have hdescent : baseEnd_1347135 < baseStart_1347135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347158 : List Nat := [5, 2, 2, 2, 1, 1, 1, 2, 6]
def baseStart_1347158 : Nat := 118140960795 + 1347158 * 2 ^ 59
def prefixEnd_1347158 : Nat := 4983230072969 + 3 ^ 40 * 1347158 * 2
def baseEnd_1347158 : Nat := 153719904788832327073231

theorem tailTrace_1347158 : CollatzResearch.WordTrace tailWord_1347158 prefixEnd_1347158 153719904788832327073231 := by
  unfold tailWord_1347158
  simp only [CollatzResearch.WordTrace]
  refine ⟨3070930553342757319637633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32756592568989411409468085 3070930553342757319637633)
  ·
    refine ⟨2303197915007067989728225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3070930553342757319637633 2303197915007067989728225)
    ·
      refine ⟨1727398436255300992296169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2303197915007067989728225 1727398436255300992296169)
      ·
        refine ⟨1295548827191475744222127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1727398436255300992296169 1295548827191475744222127)
        ·
          refine ⟨1943323240787213616333191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1295548827191475744222127 1943323240787213616333191)
          ·
            refine ⟨2914984861180820424499787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1943323240787213616333191 2914984861180820424499787)
            ·
              refine ⟨4372477291771230636749681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2914984861180820424499787 4372477291771230636749681)
              ·
                refine ⟨3279357968828422977562261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4372477291771230636749681 3279357968828422977562261)
                ·
                  refine ⟨153719904788832327073231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3279357968828422977562261 153719904788832327073231)
                  ·
                    rfl

theorem cell22_1347158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_1347158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1347158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1347158 prefixEnd_1347158 := by exact prefixLift 1347158
  have htrace : WordTrace (prefixWord ++ tailWord_1347158) baseStart_1347158 baseEnd_1347158 := by
    simpa [prefixWord, tailWord_1347158, baseEnd_1347158] using wordTrace_append hprefix tailTrace_1347158
  have hstable : (prefixWord ++ tailWord_1347158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347158).length < 2 ^ (prefixWord ++ tailWord_1347158).sum := by decide
  have hdescent : baseEnd_1347158 < baseStart_1347158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347201 : List Nat := [1, 2, 4, 2, 1, 3, 2, 1, 3, 3]
def baseStart_1347201 : Nat := 118140960795 + 1347201 * 2 ^ 59
def prefixEnd_1347201 : Nat := 4983230072969 + 3 ^ 40 * 1347201 * 2
def baseEnd_1347201 : Nat := 461174434145259202394561

theorem tailTrace_1347201 : CollatzResearch.WordTrace tailWord_1347201 prefixEnd_1347201 461174434145259202394561 := by
  unfold tailWord_1347201
  simp only [CollatzResearch.WordTrace]
  refine ⟨49136457192328335458017457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32757638128218890305344971 49136457192328335458017457)
  ·
    refine ⟨36852342894246251593513093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49136457192328335458017457 36852342894246251593513093)
    ·
      refine ⟨6909814292671172173783705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36852342894246251593513093 6909814292671172173783705)
      ·
        refine ⟨5182360719503379130337779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6909814292671172173783705 5182360719503379130337779)
        ·
          refine ⟨7773541079255068695506669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5182360719503379130337779 7773541079255068695506669)
          ·
            refine ⟨2915077904720650760815001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7773541079255068695506669 2915077904720650760815001)
            ·
              refine ⟨2186308428540488070611251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2915077904720650760815001 2186308428540488070611251)
              ·
                refine ⟨3279462642810732105916877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2186308428540488070611251 3279462642810732105916877)
                ·
                  refine ⟨1229798491054024539718829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3279462642810732105916877 1229798491054024539718829)
                  ·
                    refine ⟨461174434145259202394561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1229798491054024539718829 461174434145259202394561)
                    ·
                      rfl

theorem cell22_1347201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_1347201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1347201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1347201 prefixEnd_1347201 := by exact prefixLift 1347201
  have htrace : WordTrace (prefixWord ++ tailWord_1347201) baseStart_1347201 baseEnd_1347201 := by
    simpa [prefixWord, tailWord_1347201, baseEnd_1347201] using wordTrace_append hprefix tailTrace_1347201
  have hstable : (prefixWord ++ tailWord_1347201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347201).length < 2 ^ (prefixWord ++ tailWord_1347201).sum := by decide
  have hdescent : baseEnd_1347201 < baseStart_1347201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347212 : List Nat := [2, 2, 1, 2, 1, 1, 3, 3, 2, 5]
def baseStart_1347212 : Nat := 118140960795 + 1347212 * 2 ^ 59
def prefixEnd_1347212 : Nat := 4983230072969 + 3 ^ 40 * 1347212 * 2
def baseEnd_1347212 : Nat := 461178199670058840369527

theorem tailTrace_1347212 : CollatzResearch.WordTrace tailWord_1347212 prefixEnd_1347212 461178199670058840369527 := by
  unfold tailWord_1347212
  simp only [CollatzResearch.WordTrace]
  refine ⟨24568429197644242168333945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32757905596858989557778593 24568429197644242168333945)
  ·
    refine ⟨18426321898233181626250459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24568429197644242168333945 18426321898233181626250459)
    ·
      refine ⟨27639482847349772439375689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18426321898233181626250459 27639482847349772439375689)
      ·
        refine ⟨20729612135512329329531767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27639482847349772439375689 20729612135512329329531767)
        ·
          refine ⟨31094418203268493994297651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20729612135512329329531767 31094418203268493994297651)
          ·
            refine ⟨46641627304902740991446477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31094418203268493994297651 46641627304902740991446477)
            ·
              refine ⟨17490610239338527871792429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46641627304902740991446477 17490610239338527871792429)
              ·
                refine ⟨6558978839751947951922161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17490610239338527871792429 6558978839751947951922161)
                ·
                  refine ⟨4919234129813960963941621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6558978839751947951922161 4919234129813960963941621)
                  ·
                    refine ⟨461178199670058840369527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4919234129813960963941621 461178199670058840369527)
                    ·
                      rfl

theorem cell22_1347212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 2, 5].length) (baseStart_1347212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1347212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1347212 prefixEnd_1347212 := by exact prefixLift 1347212
  have htrace : WordTrace (prefixWord ++ tailWord_1347212) baseStart_1347212 baseEnd_1347212 := by
    simpa [prefixWord, tailWord_1347212, baseEnd_1347212] using wordTrace_append hprefix tailTrace_1347212
  have hstable : (prefixWord ++ tailWord_1347212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347212).length < 2 ^ (prefixWord ++ tailWord_1347212).sum := by decide
  have hdescent : baseEnd_1347212 < baseStart_1347212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347259 : List Nat := [1, 1, 1, 1, 1, 2, 3, 8, 4]
def baseStart_1347259 : Nat := 118140960795 + 1347259 * 2 ^ 59
def prefixEnd_1347259 : Nat := 4983230072969 + 3 ^ 40 * 1347259 * 2
def baseEnd_1347259 : Nat := 153731429576855461481461

theorem tailTrace_1347259 : CollatzResearch.WordTrace tailWord_1347259 prefixEnd_1347259 153731429576855461481461 := by
  unfold tailWord_1347259
  simp only [CollatzResearch.WordTrace]
  refine ⟨49138572626118211363628831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32759048417412140909085887 49138572626118211363628831)
  ·
    refine ⟨73707858939177317045443247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49138572626118211363628831 73707858939177317045443247)
    ·
      refine ⟨110561788408765975568164871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73707858939177317045443247 110561788408765975568164871)
      ·
        refine ⟨165842682613148963352247307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110561788408765975568164871 165842682613148963352247307)
        ·
          refine ⟨248764023919723445028370961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165842682613148963352247307 248764023919723445028370961)
          ·
            refine ⟨186573017939792583771278221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 248764023919723445028370961 186573017939792583771278221)
            ·
              refine ⟨69964881727422218914229333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 186573017939792583771278221 69964881727422218914229333)
              ·
                refine ⟨819900957743229127901125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 69964881727422218914229333 819900957743229127901125)
                ·
                  refine ⟨153731429576855461481461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 819900957743229127901125 153731429576855461481461)
                  ·
                    rfl

theorem cell22_1347259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8, 4].length) (baseStart_1347259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1347259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1347259 prefixEnd_1347259 := by exact prefixLift 1347259
  have htrace : WordTrace (prefixWord ++ tailWord_1347259) baseStart_1347259 baseEnd_1347259 := by
    simpa [prefixWord, tailWord_1347259, baseEnd_1347259] using wordTrace_append hprefix tailTrace_1347259
  have hstable : (prefixWord ++ tailWord_1347259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347259).length < 2 ^ (prefixWord ++ tailWord_1347259).sum := by decide
  have hdescent : baseEnd_1347259 < baseStart_1347259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347287 : List Nat := [1, 1, 3, 2, 1, 3, 1, 10]
def baseStart_1347287 : Nat := 118140960795 + 1347287 * 2 ^ 59
def prefixEnd_1347287 : Nat := 4983230072969 + 3 ^ 40 * 1347287 * 2
def baseEnd_1347287 : Nat := 51244874855864849416033

theorem tailTrace_1347287 : CollatzResearch.WordTrace tailWord_1347287 prefixEnd_1347287 51244874855864849416033 := by
  unfold tailWord_1347287
  simp only [CollatzResearch.WordTrace]
  refine ⟨49139593870016772145648115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32759729246677848097098743 49139593870016772145648115)
  ·
    refine ⟨73709390805025158218472173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49139593870016772145648115 73709390805025158218472173)
    ·
      refine ⟨27641021551884434331927065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73709390805025158218472173 27641021551884434331927065)
      ·
        refine ⟨20730766163913325748945299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27641021551884434331927065 20730766163913325748945299)
        ·
          refine ⟨31096149245869988623417949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20730766163913325748945299 31096149245869988623417949)
          ·
            refine ⟨11661055967201245733781731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31096149245869988623417949 11661055967201245733781731)
            ·
              refine ⟨17491583950801868600672597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11661055967201245733781731 17491583950801868600672597)
              ·
                refine ⟨51244874855864849416033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 17491583950801868600672597 51244874855864849416033)
                ·
                  rfl

theorem cell22_1347287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 10].length) (baseStart_1347287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1347287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1347287 prefixEnd_1347287 := by exact prefixLift 1347287
  have htrace : WordTrace (prefixWord ++ tailWord_1347287) baseStart_1347287 baseEnd_1347287 := by
    simpa [prefixWord, tailWord_1347287, baseEnd_1347287] using wordTrace_append hprefix tailTrace_1347287
  have hstable : (prefixWord ++ tailWord_1347287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347287).length < 2 ^ (prefixWord ++ tailWord_1347287).sum := by decide
  have hdescent : baseEnd_1347287 < baseStart_1347287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347289 : List Nat := [1, 2, 1, 2, 3, 3, 1, 3, 2, 4]
def baseStart_1347289 : Nat := 118140960795 + 1347289 * 2 ^ 59
def prefixEnd_1347289 : Nat := 4983230072969 + 3 ^ 40 * 1347289 * 2
def baseEnd_1347289 : Nat := 461204558343656306194291

theorem tailTrace_1347289 : CollatzResearch.WordTrace tailWord_1347289 prefixEnd_1347289 461204558343656306194291 := by
  unfold tailWord_1347289
  simp only [CollatzResearch.WordTrace]
  refine ⟨49139666816009526487220921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32759777877339684324813947 49139666816009526487220921)
  ·
    refine ⟨36854750112007144865415691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49139666816009526487220921 36854750112007144865415691)
    ·
      refine ⟨55282125168010717298123537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36854750112007144865415691 55282125168010717298123537)
      ·
        refine ⟨41461593876008037973592653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55282125168010717298123537 41461593876008037973592653)
        ·
          refine ⟨15548097703503014240097245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41461593876008037973592653 15548097703503014240097245)
          ·
            refine ⟨5830536638813630340036467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15548097703503014240097245 5830536638813630340036467)
            ·
              refine ⟨8745804958220445510054701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5830536638813630340036467 8745804958220445510054701)
              ·
                refine ⟨3279676859332667066270513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8745804958220445510054701 3279676859332667066270513)
                ·
                  refine ⟨2459757644499500299702885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3279676859332667066270513 2459757644499500299702885)
                  ·
                    refine ⟨461204558343656306194291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2459757644499500299702885 461204558343656306194291)
                    ·
                      rfl

theorem cell22_1347289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 3, 2, 4].length) (baseStart_1347289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1347289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1347289 prefixEnd_1347289 := by exact prefixLift 1347289
  have htrace : WordTrace (prefixWord ++ tailWord_1347289) baseStart_1347289 baseEnd_1347289 := by
    simpa [prefixWord, tailWord_1347289, baseEnd_1347289] using wordTrace_append hprefix tailTrace_1347289
  have hstable : (prefixWord ++ tailWord_1347289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347289).length < 2 ^ (prefixWord ++ tailWord_1347289).sum := by decide
  have hdescent : baseEnd_1347289 < baseStart_1347289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347336 : List Nat := [2, 1, 3, 2, 2, 1, 3, 2, 3, 3]
def baseStart_1347336 : Nat := 118140960795 + 1347336 * 2 ^ 59
def prefixEnd_1347336 : Nat := 4983230072969 + 3 ^ 40 * 1347336 * 2
def baseEnd_1347336 : Nat := 461220647404163850269147

theorem tailTrace_1347336 : CollatzResearch.WordTrace tailWord_1347336 prefixEnd_1347336 461220647404163850269147 := by
  unfold tailWord_1347336
  simp only [CollatzResearch.WordTrace]
  refine ⟨24570690523419626757090931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32760920697892835676121241 24570690523419626757090931)
  ·
    refine ⟨36856035785129440135636397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24570690523419626757090931 36856035785129440135636397)
    ·
      refine ⟨13821013419423540050863649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36856035785129440135636397 13821013419423540050863649)
      ·
        refine ⟨10365760064567655038147737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13821013419423540050863649 10365760064567655038147737)
        ·
          refine ⟨7774320048425741278610803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10365760064567655038147737 7774320048425741278610803)
          ·
            refine ⟨11661480072638611917916205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7774320048425741278610803 11661480072638611917916205)
            ·
              refine ⟨4373055027239479469218577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11661480072638611917916205 4373055027239479469218577)
              ·
                refine ⟨3279791270429609601913933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4373055027239479469218577 3279791270429609601913933)
                ·
                  refine ⟨1229921726411103600717725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3279791270429609601913933 1229921726411103600717725)
                  ·
                    refine ⟨461220647404163850269147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1229921726411103600717725 461220647404163850269147)
                    ·
                      rfl

theorem cell22_1347336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 2, 3, 3].length) (baseStart_1347336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1347336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1347336 prefixEnd_1347336 := by exact prefixLift 1347336
  have htrace : WordTrace (prefixWord ++ tailWord_1347336) baseStart_1347336 baseEnd_1347336 := by
    simpa [prefixWord, tailWord_1347336, baseEnd_1347336] using wordTrace_append hprefix tailTrace_1347336
  have hstable : (prefixWord ++ tailWord_1347336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347336).length < 2 ^ (prefixWord ++ tailWord_1347336).sum := by decide
  have hdescent : baseEnd_1347336 < baseStart_1347336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347428 : List Nat := [2, 3, 1, 1, 5, 2, 1, 1, 6]
def baseStart_1347428 : Nat := 118140960795 + 1347428 * 2 ^ 59
def prefixEnd_1347428 : Nat := 4983230072969 + 3 ^ 40 * 1347428 * 2
def baseEnd_1347428 : Nat := 153750713628102092322955

theorem tailTrace_1347428 : CollatzResearch.WordTrace tailWord_1347428 prefixEnd_1347428 153750713628102092322955 := by
  unfold tailWord_1347428
  simp only [CollatzResearch.WordTrace]
  refine ⟨24572368281252976613265469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32763157708337302151020625 24572368281252976613265469)
  ·
    refine ⟨9214638105469866229974551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24572368281252976613265469 9214638105469866229974551)
    ·
      refine ⟨13821957158204799344961827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9214638105469866229974551 13821957158204799344961827)
      ·
        refine ⟨20732935737307199017442741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13821957158204799344961827 20732935737307199017442741)
        ·
          refine ⟨1943712725372549907885257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20732935737307199017442741 1943712725372549907885257)
          ·
            refine ⟨1457784544029412430913943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1943712725372549907885257 1457784544029412430913943)
            ·
              refine ⟨2186676816044118646370915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1457784544029412430913943 2186676816044118646370915)
              ·
                refine ⟨3280015224066177969556373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2186676816044118646370915 3280015224066177969556373)
                ·
                  refine ⟨153750713628102092322955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3280015224066177969556373 153750713628102092322955)
                  ·
                    rfl

theorem cell22_1347428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 1, 6].length) (baseStart_1347428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1347428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1347428 prefixEnd_1347428 := by exact prefixLift 1347428
  have htrace : WordTrace (prefixWord ++ tailWord_1347428) baseStart_1347428 baseEnd_1347428 := by
    simpa [prefixWord, tailWord_1347428, baseEnd_1347428] using wordTrace_append hprefix tailTrace_1347428
  have hstable : (prefixWord ++ tailWord_1347428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347428).length < 2 ^ (prefixWord ++ tailWord_1347428).sum := by decide
  have hdescent : baseEnd_1347428 < baseStart_1347428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347490 : List Nat := [3, 3, 1, 2, 4, 1, 1, 7]
def baseStart_1347490 : Nat := 118140960795 + 1347490 * 2 ^ 59
def prefixEnd_1347490 : Nat := 4983230072969 + 3 ^ 40 * 1347490 * 2
def baseEnd_1347490 : Nat := 51252596083484309102075

theorem tailTrace_1347490 : CollatzResearch.WordTrace tailWord_1347490 prefixEnd_1347490 51252596083484309102075 := by
  unfold tailWord_1347490
  simp only [CollatzResearch.WordTrace]
  refine ⟨12286749472070334453821981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32764665258854225210191949 12286749472070334453821981)
  ·
    refine ⟨4607531052026375420183243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12286749472070334453821981 4607531052026375420183243)
    ·
      refine ⟨6911296578039563130274865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4607531052026375420183243 6911296578039563130274865)
      ·
        refine ⟨5183472433529672347706149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6911296578039563130274865 5183472433529672347706149)
        ·
          refine ⟨971901081286813565194903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5183472433529672347706149 971901081286813565194903)
          ·
            refine ⟨1457851621930220347792355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 971901081286813565194903 1457851621930220347792355)
            ·
              refine ⟨2186777432895330521688533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1457851621930220347792355 2186777432895330521688533)
              ·
                refine ⟨51252596083484309102075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2186777432895330521688533 51252596083484309102075)
                ·
                  rfl

theorem cell22_1347490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 7].length) (baseStart_1347490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1347490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1347490 prefixEnd_1347490 := by exact prefixLift 1347490
  have htrace : WordTrace (prefixWord ++ tailWord_1347490) baseStart_1347490 baseEnd_1347490 := by
    simpa [prefixWord, tailWord_1347490, baseEnd_1347490] using wordTrace_append hprefix tailTrace_1347490
  have hstable : (prefixWord ++ tailWord_1347490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347490).length < 2 ^ (prefixWord ++ tailWord_1347490).sum := by decide
  have hdescent : baseEnd_1347490 < baseStart_1347490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347576 : List Nat := [2, 1, 2, 1, 1, 3, 4, 1, 1, 6]
def baseStart_1347576 : Nat := 118140960795 + 1347576 * 2 ^ 59
def prefixEnd_1347576 : Nat := 4983230072969 + 3 ^ 40 * 1347576 * 2
def baseEnd_1347576 : Nat := 461302804308883224268411

theorem tailTrace_1347576 : CollatzResearch.WordTrace tailWord_1347576 prefixEnd_1347576 461302804308883224268411 := by
  unfold tailWord_1347576
  simp only [CollatzResearch.WordTrace]
  refine ⟨24575067282984887251459291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32766756377313183001945721 24575067282984887251459291)
  ·
    refine ⟨36862600924477330877188937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24575067282984887251459291 36862600924477330877188937)
    ·
      refine ⟨27646950693357998157891703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36862600924477330877188937 27646950693357998157891703)
      ·
        refine ⟨41470426040036997236837555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27646950693357998157891703 41470426040036997236837555)
        ·
          refine ⟨62205639060055495855256333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41470426040036997236837555 62205639060055495855256333)
          ·
            refine ⟨23327114647520810945721125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62205639060055495855256333 23327114647520810945721125)
            ·
              refine ⟨4373833996410152052322711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23327114647520810945721125 4373833996410152052322711)
              ·
                refine ⟨6560750994615228078484067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4373833996410152052322711 6560750994615228078484067)
                ·
                  refine ⟨9841126491922842117726101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6560750994615228078484067 9841126491922842117726101)
                  ·
                    refine ⟨461302804308883224268411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9841126491922842117726101 461302804308883224268411)
                    ·
                      rfl

theorem cell22_1347576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 1, 6].length) (baseStart_1347576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1347576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1347576 prefixEnd_1347576 := by exact prefixLift 1347576
  have htrace : WordTrace (prefixWord ++ tailWord_1347576) baseStart_1347576 baseEnd_1347576 := by
    simpa [prefixWord, tailWord_1347576, baseEnd_1347576] using wordTrace_append hprefix tailTrace_1347576
  have hstable : (prefixWord ++ tailWord_1347576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347576).length < 2 ^ (prefixWord ++ tailWord_1347576).sum := by decide
  have hdescent : baseEnd_1347576 < baseStart_1347576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347590 : List Nat := [6, 2, 1, 2, 1, 1, 3, 2, 1, 3]
def baseStart_1347590 : Nat := 118140960795 + 1347590 * 2 ^ 59
def prefixEnd_1347590 : Nat := 4983230072969 + 3 ^ 40 * 1347590 * 2
def baseEnd_1347590 : Nat := 461307596794991854418369

theorem tailTrace_1347590 : CollatzResearch.WordTrace tailWord_1347590 prefixEnd_1347590 461307596794991854418369 := by
  unfold tailWord_1347590
  simp only [CollatzResearch.WordTrace]
  refine ⟨1535957662122470465435257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 32767096791946036595952149 1535957662122470465435257)
  ·
    refine ⟨1151968246591852849076443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1535957662122470465435257 1151968246591852849076443)
    ·
      refine ⟨1727952369887779273614665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1151968246591852849076443 1727952369887779273614665)
      ·
        refine ⟨1295964277415834455210999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1727952369887779273614665 1295964277415834455210999)
        ·
          refine ⟨1943946416123751682816499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1295964277415834455210999 1943946416123751682816499)
          ·
            refine ⟨2915919624185627524224749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1943946416123751682816499 2915919624185627524224749)
            ·
              refine ⟨1093469859069610321584281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2915919624185627524224749 1093469859069610321584281)
              ·
                refine ⟨820102394302207741188211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1093469859069610321584281 820102394302207741188211)
                ·
                  refine ⟨1230153591453311611782317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 820102394302207741188211 1230153591453311611782317)
                  ·
                    refine ⟨461307596794991854418369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1230153591453311611782317 461307596794991854418369)
                    ·
                      rfl

theorem cell22_1347590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_1347590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1347590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1347590 prefixEnd_1347590 := by exact prefixLift 1347590
  have htrace : WordTrace (prefixWord ++ tailWord_1347590) baseStart_1347590 baseEnd_1347590 := by
    simpa [prefixWord, tailWord_1347590, baseEnd_1347590] using wordTrace_append hprefix tailTrace_1347590
  have hstable : (prefixWord ++ tailWord_1347590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347590).length < 2 ^ (prefixWord ++ tailWord_1347590).sum := by decide
  have hdescent : baseEnd_1347590 < baseStart_1347590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347591 : List Nat := [1, 1, 4, 3, 1, 2, 10]
def baseStart_1347591 : Nat := 118140960795 + 1347591 * 2 ^ 59
def prefixEnd_1347591 : Nat := 4983230072969 + 3 ^ 40 * 1347591 * 2
def baseEnd_1347591 : Nat := 17085479226497340190495

theorem tailTrace_1347591 : CollatzResearch.WordTrace tailWord_1347591 prefixEnd_1347591 17085479226497340190495 := by
  unfold tailWord_1347591
  simp only [CollatzResearch.WordTrace]
  refine ⟨49150681660915432064714627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32767121107276954709809751 49150681660915432064714627)
  ·
    refine ⟨73726022491373148097071941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49150681660915432064714627 73726022491373148097071941)
    ·
      refine ⟨13823629217132465268200989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73726022491373148097071941 13823629217132465268200989)
      ·
        refine ⟨5183860956424674475575371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13823629217132465268200989 5183860956424674475575371)
        ·
          refine ⟨7775791434637011713363057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5183860956424674475575371 7775791434637011713363057)
          ·
            refine ⟨5831843575977758785022293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7775791434637011713363057 5831843575977758785022293)
            ·
              refine ⟨17085479226497340190495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5831843575977758785022293 17085479226497340190495)
              ·
                rfl

theorem cell22_1347591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 10].length) (baseStart_1347591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1347591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1347591 prefixEnd_1347591 := by exact prefixLift 1347591
  have htrace : WordTrace (prefixWord ++ tailWord_1347591) baseStart_1347591 baseEnd_1347591 := by
    simpa [prefixWord, tailWord_1347591, baseEnd_1347591] using wordTrace_append hprefix tailTrace_1347591
  have hstable : (prefixWord ++ tailWord_1347591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347591).length < 2 ^ (prefixWord ++ tailWord_1347591).sum := by decide
  have hdescent : baseEnd_1347591 < baseStart_1347591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347612 : List Nat := [2, 2, 3, 1, 3, 1, 4, 1, 2, 3]
def baseStart_1347612 : Nat := 118140960795 + 1347612 * 2 ^ 59
def prefixEnd_1347612 : Nat := 4983230072969 + 3 ^ 40 * 1347612 * 2
def baseEnd_1347612 : Nat := 461315127844591130368301

theorem tailTrace_1347612 : CollatzResearch.WordTrace tailWord_1347612 prefixEnd_1347612 461315127844591130368301 := by
  unfold tailWord_1347612
  simp only [CollatzResearch.WordTrace]
  refine ⟨24575723796919676325614545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32767631729226235100819393 24575723796919676325614545)
  ·
    refine ⟨18431792847689757244210909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24575723796919676325614545 18431792847689757244210909)
    ·
      refine ⟨6911922317883658966579091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18431792847689757244210909 6911922317883658966579091)
      ·
        refine ⟨10367883476825488449868637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6911922317883658966579091 10367883476825488449868637)
        ·
          refine ⟨3887956303809558168700739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10367883476825488449868637 3887956303809558168700739)
          ·
            refine ⟨5831934455714337253051109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3887956303809558168700739 5831934455714337253051109)
            ·
              refine ⟨1093487710446438234947083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5831934455714337253051109 1093487710446438234947083)
              ·
                refine ⟨1640231565669657352420625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1093487710446438234947083 1640231565669657352420625)
                ·
                  refine ⟨1230173674252243014315469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1640231565669657352420625 1230173674252243014315469)
                  ·
                    refine ⟨461315127844591130368301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1230173674252243014315469 461315127844591130368301)
                    ·
                      rfl

theorem cell22_1347612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4, 1, 2, 3].length) (baseStart_1347612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1347612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1347612 prefixEnd_1347612 := by exact prefixLift 1347612
  have htrace : WordTrace (prefixWord ++ tailWord_1347612) baseStart_1347612 baseEnd_1347612 := by
    simpa [prefixWord, tailWord_1347612, baseEnd_1347612] using wordTrace_append hprefix tailTrace_1347612
  have hstable : (prefixWord ++ tailWord_1347612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347612).length < 2 ^ (prefixWord ++ tailWord_1347612).sum := by decide
  have hdescent : baseEnd_1347612 < baseStart_1347612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347683 : List Nat := [1, 1, 1, 5, 1, 1, 4, 1, 3, 4]
def baseStart_1347683 : Nat := 118140960795 + 1347683 * 2 ^ 59
def prefixEnd_1347683 : Nat := 4983230072969 + 3 ^ 40 * 1347683 * 2
def baseEnd_1347683 : Nat := 461339432595570611843083

theorem tailTrace_1347683 : CollatzResearch.WordTrace tailWord_1347683 prefixEnd_1347683 461339432595570611843083 := by
  unfold tailWord_1347683
  simp only [CollatzResearch.WordTrace]
  refine ⟨49154037176582131777063703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32769358117721421184709135 49154037176582131777063703)
  ·
    refine ⟨73731055764873197665595555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49154037176582131777063703 73731055764873197665595555)
    ·
      refine ⟨110596583647309796498393333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73731055764873197665595555 110596583647309796498393333)
      ·
        refine ⟨10368429716935293421724375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 110596583647309796498393333 10368429716935293421724375)
        ·
          refine ⟨15552644575402940132586563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10368429716935293421724375 15552644575402940132586563)
          ·
            refine ⟨23328966863104410198879845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15552644575402940132586563 23328966863104410198879845)
            ·
              refine ⟨4374181286832076912289971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23328966863104410198879845 4374181286832076912289971)
              ·
                refine ⟨6561271930248115368434957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4374181286832076912289971 6561271930248115368434957)
                ·
                  refine ⟨2460476973843043263163109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6561271930248115368434957 2460476973843043263163109)
                  ·
                    refine ⟨461339432595570611843083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2460476973843043263163109 461339432595570611843083)
                    ·
                      rfl

theorem cell22_1347683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 3, 4].length) (baseStart_1347683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1347683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1347683 prefixEnd_1347683 := by exact prefixLift 1347683
  have htrace : WordTrace (prefixWord ++ tailWord_1347683) baseStart_1347683 baseEnd_1347683 := by
    simpa [prefixWord, tailWord_1347683, baseEnd_1347683] using wordTrace_append hprefix tailTrace_1347683
  have hstable : (prefixWord ++ tailWord_1347683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347683).length < 2 ^ (prefixWord ++ tailWord_1347683).sum := by decide
  have hdescent : baseEnd_1347683 < baseStart_1347683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347715 : List Nat := [1, 1, 1, 3, 3, 3, 2, 4, 4]
def baseStart_1347715 : Nat := 118140960795 + 1347715 * 2 ^ 59
def prefixEnd_1347715 : Nat := 4983230072969 + 3 ^ 40 * 1347715 * 2
def baseEnd_1347715 : Nat := 153783462283177731680995

theorem tailTrace_1347715 : CollatzResearch.WordTrace tailWord_1347715 prefixEnd_1347715 153783462283177731680995 := by
  unfold tailWord_1347715
  simp only [CollatzResearch.WordTrace]
  refine ⟨49155204312466201242228599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32770136208310800828152399 49155204312466201242228599)
  ·
    refine ⟨73732806468699301863342899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49155204312466201242228599 73732806468699301863342899)
    ·
      refine ⟨110599209703048952795014349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73732806468699301863342899 110599209703048952795014349)
      ·
        refine ⟨41474703638643357298130381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110599209703048952795014349 41474703638643357298130381)
        ·
          refine ⟨15553013864491258986798893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41474703638643357298130381 15553013864491258986798893)
          ·
            refine ⟨5832380199184222120049585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15553013864491258986798893 5832380199184222120049585)
            ·
              refine ⟨4374285149388166590037189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5832380199184222120049585 4374285149388166590037189)
              ·
                refine ⟨820178465510281235631973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4374285149388166590037189 820178465510281235631973)
                ·
                  refine ⟨153783462283177731680995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 820178465510281235631973 153783462283177731680995)
                  ·
                    rfl

theorem cell22_1347715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 4, 4].length) (baseStart_1347715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1347715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1347715 prefixEnd_1347715 := by exact prefixLift 1347715
  have htrace : WordTrace (prefixWord ++ tailWord_1347715) baseStart_1347715 baseEnd_1347715 := by
    simpa [prefixWord, tailWord_1347715, baseEnd_1347715] using wordTrace_append hprefix tailTrace_1347715
  have hstable : (prefixWord ++ tailWord_1347715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347715).length < 2 ^ (prefixWord ++ tailWord_1347715).sum := by decide
  have hdescent : baseEnd_1347715 < baseStart_1347715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347773 : List Nat := [1, 4, 1, 2, 1, 1, 1, 3, 2, 6]
def baseStart_1347773 : Nat := 118140960795 + 1347773 * 2 ^ 59
def prefixEnd_1347773 : Nat := 4983230072969 + 3 ^ 40 * 1347773 * 2
def baseEnd_1347773 : Nat := 461370241434840377092807

theorem tailTrace_1347773 : CollatzResearch.WordTrace tailWord_1347773 prefixEnd_1347773 461370241434840377092807 := by
  unfold tailWord_1347773
  simp only [CollatzResearch.WordTrace]
  refine ⟨49157319746256077147839973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32771546497504051431893315 49157319746256077147839973)
  ·
    refine ⟨9216997452423014465219995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49157319746256077147839973 9216997452423014465219995)
    ·
      refine ⟨13825496178634521697829993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9216997452423014465219995 13825496178634521697829993)
      ·
        refine ⟨10369122133975891273372495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13825496178634521697829993 10369122133975891273372495)
        ·
          refine ⟨15553683200963836910058743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10369122133975891273372495 15553683200963836910058743)
          ·
            refine ⟨23330524801445755365088115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15553683200963836910058743 23330524801445755365088115)
            ·
              refine ⟨34995787202168633047632173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23330524801445755365088115 34995787202168633047632173)
              ·
                refine ⟨13123420200813237392862065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34995787202168633047632173 13123420200813237392862065)
                ·
                  refine ⟨9842565150609928044646549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13123420200813237392862065 9842565150609928044646549)
                  ·
                    refine ⟨461370241434840377092807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9842565150609928044646549 461370241434840377092807)
                    ·
                      rfl

theorem cell22_1347773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_1347773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1347773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1347773 prefixEnd_1347773 := by exact prefixLift 1347773
  have htrace : WordTrace (prefixWord ++ tailWord_1347773) baseStart_1347773 baseEnd_1347773 := by
    simpa [prefixWord, tailWord_1347773, baseEnd_1347773] using wordTrace_append hprefix tailTrace_1347773
  have hstable : (prefixWord ++ tailWord_1347773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347773).length < 2 ^ (prefixWord ++ tailWord_1347773).sum := by decide
  have hdescent : baseEnd_1347773 < baseStart_1347773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347777 : List Nat := [1, 2, 6, 1, 2, 1, 2, 7]
def baseStart_1347777 : Nat := 118140960795 + 1347777 * 2 ^ 59
def prefixEnd_1347777 : Nat := 4983230072969 + 3 ^ 40 * 1347777 * 2
def baseEnd_1347777 : Nat := 51263512301842855554755

theorem tailTrace_1347777 : CollatzResearch.WordTrace tailWord_1347777 prefixEnd_1347777 51263512301842855554755 := by
  unfold tailWord_1347777
  simp only [CollatzResearch.WordTrace]
  refine ⟨49157465638241585830985585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32771643758827723887323723 49157465638241585830985585)
  ·
    refine ⟨36868099228681189373239189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49157465638241585830985585 36868099228681189373239189)
    ·
      refine ⟨1728192151344430751870587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 36868099228681189373239189 1728192151344430751870587)
      ·
        refine ⟨2592288227016646127805881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1728192151344430751870587 2592288227016646127805881)
        ·
          refine ⟨1944216170262484595854411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2592288227016646127805881 1944216170262484595854411)
          ·
            refine ⟨2916324255393726893781617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1944216170262484595854411 2916324255393726893781617)
            ·
              refine ⟨2187243191545295170336213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2916324255393726893781617 2187243191545295170336213)
              ·
                refine ⟨51263512301842855554755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2187243191545295170336213 51263512301842855554755)
                ·
                  rfl

theorem cell22_1347777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 7].length) (baseStart_1347777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1347777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1347777 prefixEnd_1347777 := by exact prefixLift 1347777
  have htrace : WordTrace (prefixWord ++ tailWord_1347777) baseStart_1347777 baseEnd_1347777 := by
    simpa [prefixWord, tailWord_1347777, baseEnd_1347777] using wordTrace_append hprefix tailTrace_1347777
  have hstable : (prefixWord ++ tailWord_1347777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347777).length < 2 ^ (prefixWord ++ tailWord_1347777).sum := by decide
  have hdescent : baseEnd_1347777 < baseStart_1347777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347826 : List Nat := [3, 2, 1, 3, 2, 1, 4, 2, 1, 3]
def baseStart_1347826 : Nat := 118140960795 + 1347826 * 2 ^ 59
def prefixEnd_1347826 : Nat := 4983230072969 + 3 ^ 40 * 1347826 * 2
def baseEnd_1347826 : Nat := 461388384417965905517645

theorem tailTrace_1347826 : CollatzResearch.WordTrace tailWord_1347826 prefixEnd_1347826 461388384417965905517645 := by
  unfold tailWord_1347826
  simp only [CollatzResearch.WordTrace]
  refine ⟨12289813203766016799879833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32772835210042711466346221 12289813203766016799879833)
  ·
    refine ⟨9217359902824512599909875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12289813203766016799879833 9217359902824512599909875)
    ·
      refine ⟨13826039854236768899864813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9217359902824512599909875 13826039854236768899864813)
      ·
        refine ⟨5184764945338788337449305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13826039854236768899864813 5184764945338788337449305)
        ·
          refine ⟨3888573709004091253086979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5184764945338788337449305 3888573709004091253086979)
          ·
            refine ⟨5832860563506136879630469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3888573709004091253086979 5832860563506136879630469)
            ·
              refine ⟨1093661355657400664930713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5832860563506136879630469 1093661355657400664930713)
              ·
                refine ⟨820246016743050498698035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1093661355657400664930713 820246016743050498698035)
                ·
                  refine ⟨1230369025114575748047053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 820246016743050498698035 1230369025114575748047053)
                  ·
                    refine ⟨461388384417965905517645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1230369025114575748047053 461388384417965905517645)
                    ·
                      rfl

theorem cell22_1347826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4, 2, 1, 3].length) (baseStart_1347826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1347826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1347826 prefixEnd_1347826 := by exact prefixLift 1347826
  have htrace : WordTrace (prefixWord ++ tailWord_1347826) baseStart_1347826 baseEnd_1347826 := by
    simpa [prefixWord, tailWord_1347826, baseEnd_1347826] using wordTrace_append hprefix tailTrace_1347826
  have hstable : (prefixWord ++ tailWord_1347826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347826).length < 2 ^ (prefixWord ++ tailWord_1347826).sum := by decide
  have hdescent : baseEnd_1347826 < baseStart_1347826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347869 : List Nat := [1, 4, 2, 3, 2, 1, 1, 3, 1, 4]
def baseStart_1347869 : Nat := 118140960795 + 1347869 * 2 ^ 59
def prefixEnd_1347869 : Nat := 4983230072969 + 3 ^ 40 * 1347869 * 2
def baseEnd_1347869 : Nat := 461403104196728126692513

theorem tailTrace_1347869 : CollatzResearch.WordTrace tailWord_1347869 prefixEnd_1347869 461403104196728126692513 := by
  unfold tailWord_1347869
  simp only [CollatzResearch.WordTrace]
  refine ⟨49160821153908285543334661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32773880769272190362223107 49160821153908285543334661)
  ·
    refine ⟨9217653966357803539375249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49160821153908285543334661 9217653966357803539375249)
    ·
      refine ⟨6913240474768352654531437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9217653966357803539375249 6913240474768352654531437)
      ·
        refine ⟨2592465178038132245449289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6913240474768352654531437 2592465178038132245449289)
        ·
          refine ⟨1944348883528599184086967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2592465178038132245449289 1944348883528599184086967)
          ·
            refine ⟨2916523325292898776130451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1944348883528599184086967 2916523325292898776130451)
            ·
              refine ⟨4374784987939348164195677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2916523325292898776130451 4374784987939348164195677)
              ·
                refine ⟨1640544370477255561573379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4374784987939348164195677 1640544370477255561573379)
                ·
                  refine ⟨2460816555715883342360069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1640544370477255561573379 2460816555715883342360069)
                  ·
                    refine ⟨461403104196728126692513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2460816555715883342360069 461403104196728126692513)
                    ·
                      rfl

theorem cell22_1347869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_1347869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1347869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1347869 prefixEnd_1347869 := by exact prefixLift 1347869
  have htrace : WordTrace (prefixWord ++ tailWord_1347869) baseStart_1347869 baseEnd_1347869 := by
    simpa [prefixWord, tailWord_1347869, baseEnd_1347869] using wordTrace_append hprefix tailTrace_1347869
  have hstable : (prefixWord ++ tailWord_1347869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347869).length < 2 ^ (prefixWord ++ tailWord_1347869).sum := by decide
  have hdescent : baseEnd_1347869 < baseStart_1347869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347940 : List Nat := [2, 3, 1, 1, 3, 1, 1, 3, 7]
def baseStart_1347940 : Nat := 118140960795 + 1347940 * 2 ^ 59
def prefixEnd_1347940 : Nat := 4983230072969 + 3 ^ 40 * 1347940 * 2
def baseEnd_1347940 : Nat := 153809136315902536055765

theorem tailTrace_1347940 : CollatzResearch.WordTrace tailWord_1347940 prefixEnd_1347940 153809136315902536055765 := by
  unfold tailWord_1347940
  simp only [CollatzResearch.WordTrace]
  refine ⟨24581705368325532334584637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32775607157767376446112849 24581705368325532334584637)
  ·
    refine ⟨9218139513122074625469239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24581705368325532334584637 9218139513122074625469239)
    ·
      refine ⟨13827209269683111938203859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9218139513122074625469239 13827209269683111938203859)
      ·
        refine ⟨20740813904524667907305789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13827209269683111938203859 20740813904524667907305789)
        ·
          refine ⟨7777805214196750465239671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20740813904524667907305789 7777805214196750465239671)
          ·
            refine ⟨11666707821295125697859507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7777805214196750465239671 11666707821295125697859507)
            ·
              refine ⟨17500061731942688546789261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11666707821295125697859507 17500061731942688546789261)
              ·
                refine ⟨6562523149478508205045973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17500061731942688546789261 6562523149478508205045973)
                ·
                  refine ⟨153809136315902536055765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6562523149478508205045973 153809136315902536055765)
                  ·
                    rfl

theorem cell22_1347940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 7].length) (baseStart_1347940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1347940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1347940 prefixEnd_1347940 := by exact prefixLift 1347940
  have htrace : WordTrace (prefixWord ++ tailWord_1347940) baseStart_1347940 baseEnd_1347940 := by
    simpa [prefixWord, tailWord_1347940, baseEnd_1347940] using wordTrace_append hprefix tailTrace_1347940
  have hstable : (prefixWord ++ tailWord_1347940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347940).length < 2 ^ (prefixWord ++ tailWord_1347940).sum := by decide
  have hdescent : baseEnd_1347940 < baseStart_1347940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347944 : List Nat := [2, 1, 4, 2, 2, 1, 3, 1, 3, 3]
def baseStart_1347944 : Nat := 118140960795 + 1347944 * 2 ^ 59
def prefixEnd_1347944 : Nat := 4983230072969 + 3 ^ 40 * 1347944 * 2
def baseEnd_1347944 : Nat := 461428778229452931067283

theorem tailTrace_1347944 : CollatzResearch.WordTrace tailWord_1347944 prefixEnd_1347944 461428778229452931067283 := by
  unfold tailWord_1347944
  simp only [CollatzResearch.WordTrace]
  refine ⟨24581778314318286676157443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32775704419091048901543257 24581778314318286676157443)
  ·
    refine ⟨36872667471477430014236165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24581778314318286676157443 36872667471477430014236165)
    ·
      refine ⟨6913625150902018127669281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36872667471477430014236165 6913625150902018127669281)
      ·
        refine ⟨5185218863176513595751961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6913625150902018127669281 5185218863176513595751961)
        ·
          refine ⟨3888914147382385196813971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5185218863176513595751961 3888914147382385196813971)
          ·
            refine ⟨5833371221073577795220957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3888914147382385196813971 5833371221073577795220957)
            ·
              refine ⟨2187514207902591673207859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5833371221073577795220957 2187514207902591673207859)
              ·
                refine ⟨3281271311853887509811789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2187514207902591673207859 3281271311853887509811789)
                ·
                  refine ⟨1230476741945207816179421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3281271311853887509811789 1230476741945207816179421)
                  ·
                    refine ⟨461428778229452931067283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1230476741945207816179421 461428778229452931067283)
                    ·
                      rfl

theorem cell22_1347944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_1347944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1347944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1347944 prefixEnd_1347944 := by exact prefixLift 1347944
  have htrace : WordTrace (prefixWord ++ tailWord_1347944) baseStart_1347944 baseEnd_1347944 := by
    simpa [prefixWord, tailWord_1347944, baseEnd_1347944] using wordTrace_append hprefix tailTrace_1347944
  have hstable : (prefixWord ++ tailWord_1347944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347944).length < 2 ^ (prefixWord ++ tailWord_1347944).sum := by decide
  have hdescent : baseEnd_1347944 < baseStart_1347944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348002 : List Nat := [3, 3, 1, 2, 1, 1, 2, 3, 6]
def baseStart_1348002 : Nat := 118140960795 + 1348002 * 2 ^ 59
def prefixEnd_1348002 : Nat := 4983230072969 + 3 ^ 40 * 1348002 * 2
def baseEnd_1348002 : Nat := 153816210938253371039035

theorem tailTrace_1348002 : CollatzResearch.WordTrace tailWord_1348002 prefixEnd_1348002 153816210938253371039035 := by
  unfold tailWord_1348002
  simp only [CollatzResearch.WordTrace]
  refine ⟨12291418015606612314481565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32777114708284299505284173 12291418015606612314481565)
  ·
    refine ⟨4609281755852479617930587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12291418015606612314481565 4609281755852479617930587)
    ·
      refine ⟨6913922633778719426895881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4609281755852479617930587 6913922633778719426895881)
      ·
        refine ⟨5185441975334039570171911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6913922633778719426895881 5185441975334039570171911)
        ·
          refine ⟨7778162963001059355257867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5185441975334039570171911 7778162963001059355257867)
          ·
            refine ⟨11667244444501589032886801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7778162963001059355257867 11667244444501589032886801)
            ·
              refine ⟨8750433333376191774665101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11667244444501589032886801 8750433333376191774665101)
              ·
                refine ⟨3281412500016071915499413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8750433333376191774665101 3281412500016071915499413)
                ·
                  refine ⟨153816210938253371039035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3281412500016071915499413 153816210938253371039035)
                  ·
                    rfl

theorem cell22_1348002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_1348002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1348002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1348002 prefixEnd_1348002 := by exact prefixLift 1348002
  have htrace : WordTrace (prefixWord ++ tailWord_1348002) baseStart_1348002 baseEnd_1348002 := by
    simpa [prefixWord, tailWord_1348002, baseEnd_1348002] using wordTrace_append hprefix tailTrace_1348002
  have hstable : (prefixWord ++ tailWord_1348002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348002).length < 2 ^ (prefixWord ++ tailWord_1348002).sum := by decide
  have hdescent : baseEnd_1348002 < baseStart_1348002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348017 : List Nat := [1, 2, 2, 4, 1, 2, 1, 3, 1, 5]
def baseStart_1348017 : Nat := 118140960795 + 1348017 * 2 ^ 59
def prefixEnd_1348017 : Nat := 4983230072969 + 3 ^ 40 * 1348017 * 2
def baseEnd_1348017 : Nat := 461453767621305073992059

theorem tailTrace_1348017 : CollatzResearch.WordTrace tailWord_1348017 prefixEnd_1348017 461453767621305073992059 := by
  unfold tailWord_1348017
  simp only [CollatzResearch.WordTrace]
  refine ⟨49166219157372106819722305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32777479438248071213148203 49166219157372106819722305)
  ·
    refine ⟨36874664368029080114791729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49166219157372106819722305 36874664368029080114791729)
    ·
      refine ⟨27655998276021810086093797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36874664368029080114791729 27655998276021810086093797)
      ·
        refine ⟨5185499676754089391142587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27655998276021810086093797 5185499676754089391142587)
        ·
          refine ⟨7778249515131134086713881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5185499676754089391142587 7778249515131134086713881)
          ·
            refine ⟨5833687136348350565035411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7778249515131134086713881 5833687136348350565035411)
            ·
              refine ⟨8750530704522525847553117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5833687136348350565035411 8750530704522525847553117)
              ·
                refine ⟨3281449014195947192832419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8750530704522525847553117 3281449014195947192832419)
                ·
                  refine ⟨4922173521293920789248629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3281449014195947192832419 4922173521293920789248629)
                  ·
                    refine ⟨461453767621305073992059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4922173521293920789248629 461453767621305073992059)
                    ·
                      rfl

theorem cell22_1348017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 5].length) (baseStart_1348017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1348017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1348017 prefixEnd_1348017 := by exact prefixLift 1348017
  have htrace : WordTrace (prefixWord ++ tailWord_1348017) baseStart_1348017 baseEnd_1348017 := by
    simpa [prefixWord, tailWord_1348017, baseEnd_1348017] using wordTrace_append hprefix tailTrace_1348017
  have hstable : (prefixWord ++ tailWord_1348017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348017).length < 2 ^ (prefixWord ++ tailWord_1348017).sum := by decide
  have hdescent : baseEnd_1348017 < baseStart_1348017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348171 : List Nat := [1, 1, 1, 1, 3, 1, 8, 2, 4]
def baseStart_1348171 : Nat := 118140960795 + 1348171 * 2 ^ 59
def prefixEnd_1348171 : Nat := 4983230072969 + 3 ^ 40 * 1348171 * 2
def baseEnd_1348171 : Nat := 153835494989500001880529

theorem tailTrace_1348171 : CollatzResearch.WordTrace tailWord_1348171 prefixEnd_1348171 153835494989500001880529 := by
  unfold tailWord_1348171
  simp only [CollatzResearch.WordTrace]
  refine ⟨49171835998814191120828367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32781223999209460747218911 49171835998814191120828367)
  ·
    refine ⟨73757753998221286681242551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49171835998814191120828367 73757753998221286681242551)
    ·
      refine ⟨110636630997331930021863827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73757753998221286681242551 110636630997331930021863827)
      ·
        refine ⟨165954946495997895032795741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110636630997331930021863827 165954946495997895032795741)
        ·
          refine ⟨62233104935999210637298403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165954946495997895032795741 62233104935999210637298403)
          ·
            refine ⟨93349657403998815955947605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62233104935999210637298403 93349657403998815955947605)
            ·
              refine ⟨1093941297703111124483761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 93349657403998815955947605 1093941297703111124483761)
              ·
                refine ⟨820455973277333343362821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1093941297703111124483761 820455973277333343362821)
                ·
                  refine ⟨153835494989500001880529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 820455973277333343362821 153835494989500001880529)
                  ·
                    rfl

theorem cell22_1348171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8, 2, 4].length) (baseStart_1348171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1348171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1348171 prefixEnd_1348171 := by exact prefixLift 1348171
  have htrace : WordTrace (prefixWord ++ tailWord_1348171) baseStart_1348171 baseEnd_1348171 := by
    simpa [prefixWord, tailWord_1348171, baseEnd_1348171] using wordTrace_append hprefix tailTrace_1348171
  have hstable : (prefixWord ++ tailWord_1348171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348171).length < 2 ^ (prefixWord ++ tailWord_1348171).sum := by decide
  have hdescent : baseEnd_1348171 < baseStart_1348171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348231 : List Nat := [1, 1, 4, 2, 1, 2, 4, 1, 3, 3]
def baseStart_1348231 : Nat := 118140960795 + 1348231 * 2 ^ 59
def prefixEnd_1348231 : Nat := 4983230072969 + 3 ^ 40 * 1348231 * 2
def baseEnd_1348231 : Nat := 461527024194679849141403

theorem tailTrace_1348231 : CollatzResearch.WordTrace tailWord_1348231 prefixEnd_1348231 461527024194679849141403 := by
  unfold tailWord_1348231
  simp only [CollatzResearch.WordTrace]
  refine ⟨49174024378596821368012547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32782682919064547578675031 49174024378596821368012547)
  ·
    refine ⟨73761036567895232052018821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49174024378596821368012547 73761036567895232052018821)
    ·
      refine ⟨13830194356480356009753529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73761036567895232052018821 13830194356480356009753529)
      ·
        refine ⟨10372645767360267007315147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13830194356480356009753529 10372645767360267007315147)
        ·
          refine ⟨15558968651040400510972721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10372645767360267007315147 15558968651040400510972721)
          ·
            refine ⟨11669226488280300383229541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15558968651040400510972721 11669226488280300383229541)
            ·
              refine ⟨2187979966552556321855539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11669226488280300383229541 2187979966552556321855539)
              ·
                refine ⟨3281969949828834482783309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2187979966552556321855539 3281969949828834482783309)
                ·
                  refine ⟨1230738731185812931043741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3281969949828834482783309 1230738731185812931043741)
                  ·
                    refine ⟨461527024194679849141403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1230738731185812931043741 461527024194679849141403)
                    ·
                      rfl

theorem cell22_1348231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 1, 3, 3].length) (baseStart_1348231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1348231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1348231 prefixEnd_1348231 := by exact prefixLift 1348231
  have htrace : WordTrace (prefixWord ++ tailWord_1348231) baseStart_1348231 baseEnd_1348231 := by
    simpa [prefixWord, tailWord_1348231, baseEnd_1348231] using wordTrace_append hprefix tailTrace_1348231
  have hstable : (prefixWord ++ tailWord_1348231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348231).length < 2 ^ (prefixWord ++ tailWord_1348231).sum := by decide
  have hdescent : baseEnd_1348231 < baseStart_1348231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348250 : List Nat := [3, 1, 1, 6, 2, 1, 2, 6]
def baseStart_1348250 : Nat := 118140960795 + 1348250 * 2 ^ 59
def prefixEnd_1348250 : Nat := 4983230072969 + 3 ^ 40 * 1348250 * 2
def baseEnd_1348250 : Nat := 51281503142552236990705

theorem tailTrace_1348250 : CollatzResearch.WordTrace tailWord_1348250 prefixEnd_1348250 51281503142552236990705 := by
  unfold tailWord_1348250
  simp only [CollatzResearch.WordTrace]
  refine ⟨12293679341381996903238551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32783144910351991741969469 12293679341381996903238551)
  ·
    refine ⟨18440519012072995354857827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12293679341381996903238551 18440519012072995354857827)
    ·
      refine ⟨27660778518109493032286741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18440519012072995354857827 27660778518109493032286741)
      ·
        refine ⟨1296598993036382485888441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 27660778518109493032286741 1296598993036382485888441)
        ·
          refine ⟨972449244777286864416331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1296598993036382485888441 972449244777286864416331)
          ·
            refine ⟨1458673867165930296624497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 972449244777286864416331 1458673867165930296624497)
            ·
              refine ⟨1094005400374447722468373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1458673867165930296624497 1094005400374447722468373)
              ·
                refine ⟨51281503142552236990705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1094005400374447722468373 51281503142552236990705)
                ·
                  rfl

theorem cell22_1348250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 2, 6].length) (baseStart_1348250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1348250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1348250 prefixEnd_1348250 := by exact prefixLift 1348250
  have htrace : WordTrace (prefixWord ++ tailWord_1348250) baseStart_1348250 baseEnd_1348250 := by
    simpa [prefixWord, tailWord_1348250, baseEnd_1348250] using wordTrace_append hprefix tailTrace_1348250
  have hstable : (prefixWord ++ tailWord_1348250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348250).length < 2 ^ (prefixWord ++ tailWord_1348250).sum := by decide
  have hdescent : baseEnd_1348250 < baseStart_1348250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348274 : List Nat := [3, 2, 1, 1, 1, 2, 1, 2, 5, 4]
def baseStart_1348274 : Nat := 118140960795 + 1348274 * 2 ^ 59
def prefixEnd_1348274 : Nat := 4983230072969 + 3 ^ 40 * 1348274 * 2
def baseEnd_1348274 : Nat := 461541743973442070316271

theorem tailTrace_1348274 : CollatzResearch.WordTrace tailWord_1348274 prefixEnd_1348274 461541743973442070316271 := by
  unfold tailWord_1348274
  simp only [CollatzResearch.WordTrace]
  refine ⟨12293898179360259927956969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32783728478294026474551917 12293898179360259927956969)
  ·
    refine ⟨9220423634520194945967727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12293898179360259927956969 9220423634520194945967727)
    ·
      refine ⟨13830635451780292418951591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9220423634520194945967727 13830635451780292418951591)
      ·
        refine ⟨20745953177670438628427387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13830635451780292418951591 20745953177670438628427387)
        ·
          refine ⟨31118929766505657942641081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20745953177670438628427387 31118929766505657942641081)
          ·
            refine ⟨23339197324879243456980811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31118929766505657942641081 23339197324879243456980811)
            ·
              refine ⟨35008795987318865185471217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23339197324879243456980811 35008795987318865185471217)
              ·
                refine ⟨26256596990489148889103413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35008795987318865185471217 26256596990489148889103413)
                ·
                  refine ⟨2461555967858357708353445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26256596990489148889103413 2461555967858357708353445)
                  ·
                    refine ⟨461541743973442070316271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2461555967858357708353445 461541743973442070316271)
                    ·
                      rfl

theorem cell22_1348274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_1348274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1348274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1348274 prefixEnd_1348274 := by exact prefixLift 1348274
  have htrace : WordTrace (prefixWord ++ tailWord_1348274) baseStart_1348274 baseEnd_1348274 := by
    simpa [prefixWord, tailWord_1348274, baseEnd_1348274] using wordTrace_append hprefix tailTrace_1348274
  have hstable : (prefixWord ++ tailWord_1348274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348274).length < 2 ^ (prefixWord ++ tailWord_1348274).sum := by decide
  have hdescent : baseEnd_1348274 < baseStart_1348274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348308 : List Nat := [2, 4, 1, 3, 2, 1, 1, 1, 3, 4]
def baseStart_1348308 : Nat := 118140960795 + 1348308 * 2 ^ 59
def prefixEnd_1348308 : Nat := 4983230072969 + 3 ^ 40 * 1348308 * 2
def baseEnd_1348308 : Nat := 461553382868277314966167

theorem tailTrace_1348308 : CollatzResearch.WordTrace tailWord_1348308 prefixEnd_1348308 461553382868277314966167 := by
  unfold tailWord_1348308
  simp only [CollatzResearch.WordTrace]
  refine ⟨24588416399658931759282789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32784555199545242345710385 24588416399658931759282789)
  ·
    refine ⟨4610328074936049704865523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24588416399658931759282789 4610328074936049704865523)
    ·
      refine ⟨6915492112404074557298285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4610328074936049704865523 6915492112404074557298285)
      ·
        refine ⟨2593309542151527958986857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6915492112404074557298285 2593309542151527958986857)
        ·
          refine ⟨1944982156613645969240143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2593309542151527958986857 1944982156613645969240143)
          ·
            refine ⟨2917473234920468953860215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1944982156613645969240143 2917473234920468953860215)
            ·
              refine ⟨4376209852380703430790323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2917473234920468953860215 4376209852380703430790323)
              ·
                refine ⟨6564314778571055146185485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4376209852380703430790323 6564314778571055146185485)
                ·
                  refine ⟨2461618041964145679819557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6564314778571055146185485 2461618041964145679819557)
                  ·
                    refine ⟨461553382868277314966167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2461618041964145679819557 461553382868277314966167)
                    ·
                      rfl

theorem cell22_1348308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_1348308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1348308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1348308 prefixEnd_1348308 := by exact prefixLift 1348308
  have htrace : WordTrace (prefixWord ++ tailWord_1348308) baseStart_1348308 baseEnd_1348308 := by
    simpa [prefixWord, tailWord_1348308, baseEnd_1348308] using wordTrace_append hprefix tailTrace_1348308
  have hstable : (prefixWord ++ tailWord_1348308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348308).length < 2 ^ (prefixWord ++ tailWord_1348308).sum := by decide
  have hdescent : baseEnd_1348308 < baseStart_1348308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348321 : List Nat := [1, 2, 3, 1, 4, 2, 1, 2, 1, 5]
def baseStart_1348321 : Nat := 118140960795 + 1348321 * 2 ^ 59
def prefixEnd_1348321 : Nat := 4983230072969 + 3 ^ 40 * 1348321 * 2
def baseEnd_1348321 : Nat := 461557833033949614391127

theorem tailTrace_1348321 : CollatzResearch.WordTrace tailWord_1348321 prefixEnd_1348321 461557833033949614391127 := by
  unfold tailWord_1348321
  simp only [CollatzResearch.WordTrace]
  refine ⟨49177306948270766738788817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32784871298847177825859211 49177306948270766738788817)
  ·
    refine ⟨36882980211203075054091613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49177306948270766738788817 36882980211203075054091613)
    ·
      refine ⟨13831117579201153145284355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36882980211203075054091613 13831117579201153145284355)
      ·
        refine ⟨20746676368801729717926533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13831117579201153145284355 20746676368801729717926533)
        ·
          refine ⟨3890001819150324322111225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20746676368801729717926533 3890001819150324322111225)
          ·
            refine ⟨2917501364362743241583419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3890001819150324322111225 2917501364362743241583419)
            ·
              refine ⟨4376252046544114862375129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2917501364362743241583419 4376252046544114862375129)
              ·
                refine ⟨3282189034908086146781347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4376252046544114862375129 3282189034908086146781347)
                ·
                  refine ⟨4923283552362129220172021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3282189034908086146781347 4923283552362129220172021)
                  ·
                    refine ⟨461557833033949614391127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4923283552362129220172021 461557833033949614391127)
                    ·
                      rfl

theorem cell22_1348321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_1348321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1348321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1348321 prefixEnd_1348321 := by exact prefixLift 1348321
  have htrace : WordTrace (prefixWord ++ tailWord_1348321) baseStart_1348321 baseEnd_1348321 := by
    simpa [prefixWord, tailWord_1348321, baseEnd_1348321] using wordTrace_append hprefix tailTrace_1348321
  have hstable : (prefixWord ++ tailWord_1348321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348321).length < 2 ^ (prefixWord ++ tailWord_1348321).sum := by decide
  have hdescent : baseEnd_1348321 < baseStart_1348321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348334 : List Nat := [4, 1, 2, 1, 1, 13]
def baseStart_1348334 : Nat := 118140960795 + 1348334 * 2 ^ 59
def prefixEnd_1348334 : Nat := 4983230072969 + 3 ^ 40 * 1348334 * 2
def baseEnd_1348334 : Nat := 5698299792587924861927

theorem tailTrace_1348334 : CollatzResearch.WordTrace tailWord_1348334 prefixEnd_1348334 5698299792587924861927 := by
  unfold tailWord_1348334
  simp only [CollatzResearch.WordTrace]
  refine ⟨6147222637152958744876507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32785187398149113306008037 6147222637152958744876507)
  ·
    refine ⟨9220833955729438117314761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6147222637152958744876507 9220833955729438117314761)
    ·
      refine ⟨6915625466797078587986071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9220833955729438117314761 6915625466797078587986071)
      ·
        refine ⟨10373438200195617881979107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6915625466797078587986071 10373438200195617881979107)
        ·
          refine ⟨15560157300293426822968661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10373438200195617881979107 15560157300293426822968661)
          ·
            refine ⟨5698299792587924861927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 15560157300293426822968661 5698299792587924861927)
            ·
              rfl

theorem cell22_1348334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 13].length) (baseStart_1348334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1348334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1348334 prefixEnd_1348334 := by exact prefixLift 1348334
  have htrace : WordTrace (prefixWord ++ tailWord_1348334) baseStart_1348334 baseEnd_1348334 := by
    simpa [prefixWord, tailWord_1348334, baseEnd_1348334] using wordTrace_append hprefix tailTrace_1348334
  have hstable : (prefixWord ++ tailWord_1348334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348334).length < 2 ^ (prefixWord ++ tailWord_1348334).sum := by decide
  have hdescent : baseEnd_1348334 < baseStart_1348334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348338 : List Nat := [3, 2, 1, 3, 1, 2, 1, 4, 2, 3]
def baseStart_1348338 : Nat := 118140960795 + 1348338 * 2 ^ 59
def prefixEnd_1348338 : Nat := 4983230072969 + 3 ^ 40 * 1348338 * 2
def baseEnd_1348338 : Nat := 461563652481367236716075

theorem tailTrace_1348338 : CollatzResearch.WordTrace tailWord_1348338 prefixEnd_1348338 461563652481367236716075 := by
  unfold tailWord_1348338
  simp only [CollatzResearch.WordTrace]
  refine ⟨12294481747302294660539417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32785284659472785761438445 12294481747302294660539417)
  ·
    refine ⟨9220861310476720995404563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12294481747302294660539417 9220861310476720995404563)
    ·
      refine ⟨13831291965715081493106845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9220861310476720995404563 13831291965715081493106845)
      ·
        refine ⟨5186734487143155559915067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13831291965715081493106845 5186734487143155559915067)
        ·
          refine ⟨7780101730714733339872601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5186734487143155559915067 7780101730714733339872601)
          ·
            refine ⟨5835076298036050004904451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7780101730714733339872601 5835076298036050004904451)
            ·
              refine ⟨8752614447054075007356677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5835076298036050004904451 8752614447054075007356677)
              ·
                refine ⟨1641115208822639063879377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8752614447054075007356677 1641115208822639063879377)
                ·
                  refine ⟨1230836406616979297909533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1641115208822639063879377 1230836406616979297909533)
                  ·
                    refine ⟨461563652481367236716075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1230836406616979297909533 461563652481367236716075)
                    ·
                      rfl

theorem cell22_1348338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 4, 2, 3].length) (baseStart_1348338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1348338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1348338 prefixEnd_1348338 := by exact prefixLift 1348338
  have htrace : WordTrace (prefixWord ++ tailWord_1348338) baseStart_1348338 baseEnd_1348338 := by
    simpa [prefixWord, tailWord_1348338, baseEnd_1348338] using wordTrace_append hprefix tailTrace_1348338
  have hstable : (prefixWord ++ tailWord_1348338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348338).length < 2 ^ (prefixWord ++ tailWord_1348338).sum := by decide
  have hdescent : baseEnd_1348338 < baseStart_1348338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348364 : List Nat := [2, 2, 1, 2, 2, 1, 1, 1, 4, 6]
def baseStart_1348364 : Nat := 118140960795 + 1348364 * 2 ^ 59
def prefixEnd_1348364 : Nat := 4983230072969 + 3 ^ 40 * 1348364 * 2
def baseEnd_1348364 : Nat := 461572552812711835565995

theorem tailTrace_1348364 : CollatzResearch.WordTrace tailWord_1348364 prefixEnd_1348364 461572552812711835565995 := by
  unfold tailWord_1348364
  simp only [CollatzResearch.WordTrace]
  refine ⟨24589437643557492541302073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32785916858076656721736097 24589437643557492541302073)
  ·
    refine ⟨18442078232668119405976555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24589437643557492541302073 18442078232668119405976555)
    ·
      refine ⟨27663117349002179108964833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18442078232668119405976555 27663117349002179108964833)
      ·
        refine ⟨20747338011751634331723625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27663117349002179108964833 20747338011751634331723625)
        ·
          refine ⟨15560503508813725748792719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20747338011751634331723625 15560503508813725748792719)
          ·
            refine ⟨23340755263220588623189079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15560503508813725748792719 23340755263220588623189079)
            ·
              refine ⟨35011132894830882934783619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23340755263220588623189079 35011132894830882934783619)
              ·
                refine ⟨52516699342246324402175429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35011132894830882934783619 52516699342246324402175429)
                ·
                  refine ⟨9846881126671185825407893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52516699342246324402175429 9846881126671185825407893)
                  ·
                    refine ⟨461572552812711835565995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9846881126671185825407893 461572552812711835565995)
                    ·
                      rfl

theorem cell22_1348364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 4, 6].length) (baseStart_1348364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1348364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1348364 prefixEnd_1348364 := by exact prefixLift 1348364
  have htrace : WordTrace (prefixWord ++ tailWord_1348364) baseStart_1348364 baseEnd_1348364 := by
    simpa [prefixWord, tailWord_1348364, baseEnd_1348364] using wordTrace_append hprefix tailTrace_1348364
  have hstable : (prefixWord ++ tailWord_1348364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348364).length < 2 ^ (prefixWord ++ tailWord_1348364).sum := by decide
  have hdescent : baseEnd_1348364 < baseStart_1348364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348488 : List Nat := [2, 1, 3, 3, 2, 1, 1, 3, 2, 4]
def baseStart_1348488 : Nat := 118140960795 + 1348488 * 2 ^ 59
def prefixEnd_1348488 : Nat := 4983230072969 + 3 ^ 40 * 1348488 * 2
def baseEnd_1348488 : Nat := 461615000546816845465615

theorem tailTrace_1348488 : CollatzResearch.WordTrace tailWord_1348488 prefixEnd_1348488 461615000546816845465615 := by
  unfold tailWord_1348488
  simp only [CollatzResearch.WordTrace]
  refine ⟨24591698969332877130059059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32788931959110502840078745 24591698969332877130059059)
  ·
    refine ⟨36887548453999315695088589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24591698969332877130059059 36887548453999315695088589)
    ·
      refine ⟨13832830670249743385658221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36887548453999315695088589 13832830670249743385658221)
      ·
        refine ⟨5187311501343653769621833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13832830670249743385658221 5187311501343653769621833)
        ·
          refine ⟨3890483626007740327216375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5187311501343653769621833 3890483626007740327216375)
          ·
            refine ⟨5835725439011610490824563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3890483626007740327216375 5835725439011610490824563)
            ·
              refine ⟨8753588158517415736236845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5835725439011610490824563 8753588158517415736236845)
              ·
                refine ⟨3282595559444030901088817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8753588158517415736236845 3282595559444030901088817)
                ·
                  refine ⟨2461946669583023175816613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3282595559444030901088817 2461946669583023175816613)
                  ·
                    refine ⟨461615000546816845465615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2461946669583023175816613 461615000546816845465615)
                    ·
                      rfl

theorem cell22_1348488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_1348488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1348488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1348488 prefixEnd_1348488 := by exact prefixLift 1348488
  have htrace : WordTrace (prefixWord ++ tailWord_1348488) baseStart_1348488 baseEnd_1348488 := by
    simpa [prefixWord, tailWord_1348488, baseEnd_1348488] using wordTrace_append hprefix tailTrace_1348488
  have hstable : (prefixWord ++ tailWord_1348488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348488).length < 2 ^ (prefixWord ++ tailWord_1348488).sum := by decide
  have hdescent : baseEnd_1348488 < baseStart_1348488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348516 : List Nat := [2, 3, 1, 2, 1, 2, 1, 1, 1, 8]
def baseStart_1348516 : Nat := 118140960795 + 1348516 * 2 ^ 59
def prefixEnd_1348516 : Nat := 4983230072969 + 3 ^ 40 * 1348516 * 2
def baseEnd_1348516 : Nat := 461624585519034105765529

theorem tailTrace_1348516 : CollatzResearch.WordTrace tailWord_1348516 prefixEnd_1348516 461624585519034105765529 := by
  unfold tailWord_1348516
  simp only [CollatzResearch.WordTrace]
  refine ⟨24592209591282157521068701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32789612788376210028091601 24592209591282157521068701)
  ·
    refine ⟨9222078596730809070400763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24592209591282157521068701 9222078596730809070400763)
    ·
      refine ⟨13833117895096213605601145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9222078596730809070400763 13833117895096213605601145)
      ·
        refine ⟨10374838421322160204200859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13833117895096213605601145 10374838421322160204200859)
        ·
          refine ⟨15562257631983240306301289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10374838421322160204200859 15562257631983240306301289)
          ·
            refine ⟨11671693223987430229725967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15562257631983240306301289 11671693223987430229725967)
            ·
              refine ⟨17507539835981145344588951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11671693223987430229725967 17507539835981145344588951)
              ·
                refine ⟨26261309753971718016883427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17507539835981145344588951 26261309753971718016883427)
                ·
                  refine ⟨39391964630957577025325141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26261309753971718016883427 39391964630957577025325141)
                  ·
                    refine ⟨461624585519034105765529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 39391964630957577025325141 461624585519034105765529)
                    ·
                      rfl

theorem cell22_1348516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_1348516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1348516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1348516 prefixEnd_1348516 := by exact prefixLift 1348516
  have htrace : WordTrace (prefixWord ++ tailWord_1348516) baseStart_1348516 baseEnd_1348516 := by
    simpa [prefixWord, tailWord_1348516, baseEnd_1348516] using wordTrace_append hprefix tailTrace_1348516
  have hstable : (prefixWord ++ tailWord_1348516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348516).length < 2 ^ (prefixWord ++ tailWord_1348516).sum := by decide
  have hdescent : baseEnd_1348516 < baseStart_1348516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348593 : List Nat := [1, 2, 2, 2, 4, 1, 2, 2, 6]
def baseStart_1348593 : Nat := 118140960795 + 1348593 * 2 ^ 59
def prefixEnd_1348593 : Nat := 4983230072969 + 3 ^ 40 * 1348593 * 2
def baseEnd_1348593 : Nat := 153883648064210523863431

theorem tailTrace_1348593 : CollatzResearch.WordTrace tailWord_1348593 prefixEnd_1348593 153883648064210523863431 := by
  unfold tailWord_1348593
  simp only [CollatzResearch.WordTrace]
  refine ⟨49187227603285357192690433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32791485068856904795126955 49187227603285357192690433)
  ·
    refine ⟨36890420702464017894517825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49187227603285357192690433 36890420702464017894517825)
    ·
      refine ⟨27667815526848013420888369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36890420702464017894517825 27667815526848013420888369)
      ·
        refine ⟨20750861645136010065666277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27667815526848013420888369 20750861645136010065666277)
        ·
          refine ⟨3890786558463001887312427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20750861645136010065666277 3890786558463001887312427)
          ·
            refine ⟨5836179837694502830968641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3890786558463001887312427 5836179837694502830968641)
            ·
              refine ⟨4377134878270877123226481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5836179837694502830968641 4377134878270877123226481)
              ·
                refine ⟨3282851158703157842419861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4377134878270877123226481 3282851158703157842419861)
                ·
                  refine ⟨153883648064210523863431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3282851158703157842419861 153883648064210523863431)
                  ·
                    rfl

theorem cell22_1348593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 2, 6].length) (baseStart_1348593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1348593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1348593 prefixEnd_1348593 := by exact prefixLift 1348593
  have htrace : WordTrace (prefixWord ++ tailWord_1348593) baseStart_1348593 baseEnd_1348593 := by
    simpa [prefixWord, tailWord_1348593, baseEnd_1348593] using wordTrace_append hprefix tailTrace_1348593
  have hstable : (prefixWord ++ tailWord_1348593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348593).length < 2 ^ (prefixWord ++ tailWord_1348593).sum := by decide
  have hdescent : baseEnd_1348593 < baseStart_1348593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348642 : List Nat := [3, 3, 1, 1, 1, 4, 1, 3, 2, 3]
def baseStart_1348642 : Nat := 118140960795 + 1348642 * 2 ^ 59
def prefixEnd_1348642 : Nat := 4983230072969 + 3 ^ 40 * 1348642 * 2
def baseEnd_1348642 : Nat := 461667717894011777115143

theorem tailTrace_1348642 : CollatzResearch.WordTrace tailWord_1348642 prefixEnd_1348642 461667717894011777115143 := by
  unfold tailWord_1348642
  simp only [CollatzResearch.WordTrace]
  refine ⟨12297253695026959640306045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32792676520071892374149453 12297253695026959640306045)
  ·
    refine ⟨4611470135635109865114767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12297253695026959640306045 4611470135635109865114767)
    ·
      refine ⟨6917205203452664797672151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4611470135635109865114767 6917205203452664797672151)
      ·
        refine ⟨10375807805178997196508227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6917205203452664797672151 10375807805178997196508227)
        ·
          refine ⟨15563711707768495794762341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10375807805178997196508227 15563711707768495794762341)
          ·
            refine ⟨2918195945206592961517939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15563711707768495794762341 2918195945206592961517939)
            ·
              refine ⟨4377293917809889442276909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2918195945206592961517939 4377293917809889442276909)
              ·
                refine ⟨1641485219178708540853841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4377293917809889442276909 1641485219178708540853841)
                ·
                  refine ⟨1231113914384031405640381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1641485219178708540853841 1231113914384031405640381)
                  ·
                    refine ⟨461667717894011777115143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1231113914384031405640381 461667717894011777115143)
                    ·
                      rfl

theorem cell22_1348642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_1348642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1348642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1348642 prefixEnd_1348642 := by exact prefixLift 1348642
  have htrace : WordTrace (prefixWord ++ tailWord_1348642) baseStart_1348642 baseEnd_1348642 := by
    simpa [prefixWord, tailWord_1348642, baseEnd_1348642] using wordTrace_append hprefix tailTrace_1348642
  have hstable : (prefixWord ++ tailWord_1348642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348642).length < 2 ^ (prefixWord ++ tailWord_1348642).sum := by decide
  have hdescent : baseEnd_1348642 < baseStart_1348642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348685 : List Nat := [1, 6, 1, 1, 1, 2, 1, 1, 2, 6]
def baseStart_1348685 : Nat := 118140960795 + 1348685 * 2 ^ 59
def prefixEnd_1348685 : Nat := 4983230072969 + 3 ^ 40 * 1348685 * 2
def baseEnd_1348685 : Nat := 461682437672773998290011

theorem tailTrace_1348685 : CollatzResearch.WordTrace tailWord_1348685 prefixEnd_1348685 461682437672773998290011 := by
  unfold tailWord_1348685
  simp only [CollatzResearch.WordTrace]
  refine ⟨49190583118952056905039509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32793722079301371270026339 49190583118952056905039509)
  ·
    refine ⟨2305808583700877667423727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 49190583118952056905039509 2305808583700877667423727)
    ·
      refine ⟨3458712875551316501135591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2305808583700877667423727 3458712875551316501135591)
      ·
        refine ⟨5188069313326974751703387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3458712875551316501135591 5188069313326974751703387)
        ·
          refine ⟨7782103969990462127555081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5188069313326974751703387 7782103969990462127555081)
          ·
            refine ⟨5836577977492846595666311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7782103969990462127555081 5836577977492846595666311)
            ·
              refine ⟨8754866966239269893499467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5836577977492846595666311 8754866966239269893499467)
              ·
                refine ⟨13132300449358904840249201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8754866966239269893499467 13132300449358904840249201)
                ·
                  refine ⟨9849225337019178630186901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13132300449358904840249201 9849225337019178630186901)
                  ·
                    refine ⟨461682437672773998290011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9849225337019178630186901 461682437672773998290011)
                    ·
                      rfl

theorem cell22_1348685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_1348685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1348685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1348685 prefixEnd_1348685 := by exact prefixLift 1348685
  have htrace : WordTrace (prefixWord ++ tailWord_1348685) baseStart_1348685 baseEnd_1348685 := by
    simpa [prefixWord, tailWord_1348685, baseEnd_1348685] using wordTrace_append hprefix tailTrace_1348685
  have hstable : (prefixWord ++ tailWord_1348685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348685).length < 2 ^ (prefixWord ++ tailWord_1348685).sum := by decide
  have hdescent : baseEnd_1348685 < baseStart_1348685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348700 : List Nat := [2, 2, 4, 1, 1, 1, 1, 5, 5]
def baseStart_1348700 : Nat := 118140960795 + 1348700 * 2 ^ 59
def prefixEnd_1348700 : Nat := 4983230072969 + 3 ^ 40 * 1348700 * 2
def baseEnd_1348700 : Nat := 153895857493106319721655

theorem tailTrace_1348700 : CollatzResearch.WordTrace tailWord_1348700 prefixEnd_1348700 153895857493106319721655 := by
  unfold tailWord_1348700
  simp only [CollatzResearch.WordTrace]
  refine ⟨24595565106948857233417777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32794086809265142977890369 24595565106948857233417777)
  ·
    refine ⟨18446673830211642925063333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24595565106948857233417777 18446673830211642925063333)
    ·
      refine ⟨3458751343164683048449375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18446673830211642925063333 3458751343164683048449375)
      ·
        refine ⟨5188127014747024572674063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3458751343164683048449375 5188127014747024572674063)
        ·
          refine ⟨7782190522120536859011095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5188127014747024572674063 7782190522120536859011095)
          ·
            refine ⟨11673285783180805288516643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7782190522120536859011095 11673285783180805288516643)
            ·
              refine ⟨17509928674771207932774965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11673285783180805288516643 17509928674771207932774965)
              ·
                refine ⟨1641555813259800743697653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17509928674771207932774965 1641555813259800743697653)
                ·
                  refine ⟨153895857493106319721655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1641555813259800743697653 153895857493106319721655)
                  ·
                    rfl

theorem cell22_1348700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 5, 5].length) (baseStart_1348700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1348700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1348700 prefixEnd_1348700 := by exact prefixLift 1348700
  have htrace : WordTrace (prefixWord ++ tailWord_1348700) baseStart_1348700 baseEnd_1348700 := by
    simpa [prefixWord, tailWord_1348700, baseEnd_1348700] using wordTrace_append hprefix tailTrace_1348700
  have hstable : (prefixWord ++ tailWord_1348700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348700).length < 2 ^ (prefixWord ++ tailWord_1348700).sum := by decide
  have hdescent : baseEnd_1348700 < baseStart_1348700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348745 : List Nat := [1, 2, 1, 1, 4, 4, 2, 1, 6]
def baseStart_1348745 : Nat := 118140960795 + 1348745 * 2 ^ 59
def prefixEnd_1348745 : Nat := 4983230072969 + 3 ^ 40 * 1348745 * 2
def baseEnd_1348745 : Nat := 153900992299651280596609

theorem tailTrace_1348745 : CollatzResearch.WordTrace tailWord_1348745 prefixEnd_1348745 153900992299651280596609 := by
  unfold tailWord_1348745
  simp only [CollatzResearch.WordTrace]
  refine ⟨49192771498734687152223689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32795180999156458101482459 49192771498734687152223689)
  ·
    refine ⟨36894578624051015364167767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49192771498734687152223689 36894578624051015364167767)
    ·
      refine ⟨55341867936076523046251651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36894578624051015364167767 55341867936076523046251651)
      ·
        refine ⟨83012801904114784569377477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55341867936076523046251651 83012801904114784569377477)
        ·
          refine ⟨15564900357021522106758277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83012801904114784569377477 15564900357021522106758277)
          ·
            refine ⟨2918418816941535395017177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15564900357021522106758277 2918418816941535395017177)
            ·
              refine ⟨2188814112706151546262883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2918418816941535395017177 2188814112706151546262883)
              ·
                refine ⟨3283221169059227319394325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2188814112706151546262883 3283221169059227319394325)
                ·
                  refine ⟨153900992299651280596609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3283221169059227319394325 153900992299651280596609)
                  ·
                    rfl

theorem cell22_1348745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 1, 6].length) (baseStart_1348745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1348745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1348745 prefixEnd_1348745 := by exact prefixLift 1348745
  have htrace : WordTrace (prefixWord ++ tailWord_1348745) baseStart_1348745 baseEnd_1348745 := by
    simpa [prefixWord, tailWord_1348745, baseEnd_1348745] using wordTrace_append hprefix tailTrace_1348745
  have hstable : (prefixWord ++ tailWord_1348745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348745).length < 2 ^ (prefixWord ++ tailWord_1348745).sum := by decide
  have hdescent : baseEnd_1348745 < baseStart_1348745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348899 : List Nat := [1, 1, 1, 4, 2, 3, 4, 1, 1, 4]
def baseStart_1348899 : Nat := 118140960795 + 1348899 * 2 ^ 59
def prefixEnd_1348899 : Nat := 4983230072969 + 3 ^ 40 * 1348899 * 2
def baseEnd_1348899 : Nat := 461755694246148773439355

theorem tailTrace_1348899 : CollatzResearch.WordTrace tailWord_1348899 prefixEnd_1348899 461755694246148773439355 := by
  unfold tailWord_1348899
  simp only [CollatzResearch.WordTrace]
  refine ⟨49198388340176771453329751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32798925560117847635553167 49198388340176771453329751)
  ·
    refine ⟨73797582510265157179994627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49198388340176771453329751 73797582510265157179994627)
    ·
      refine ⟨110696373765397735769991941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73797582510265157179994627 110696373765397735769991941)
      ·
        refine ⟨20755570081012075456873489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110696373765397735769991941 20755570081012075456873489)
        ·
          refine ⟨15566677560759056592655117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20755570081012075456873489 15566677560759056592655117)
          ·
            refine ⟨5837504085284646222245669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15566677560759056592655117 5837504085284646222245669)
            ·
              refine ⟨1094532015990871166671063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5837504085284646222245669 1094532015990871166671063)
              ·
                refine ⟨1641798023986306750006595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1094532015990871166671063 1641798023986306750006595)
                ·
                  refine ⟨2462697035979460125009893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1641798023986306750006595 2462697035979460125009893)
                  ·
                    refine ⟨461755694246148773439355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2462697035979460125009893 461755694246148773439355)
                    ·
                      rfl

theorem cell22_1348899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4, 1, 1, 4].length) (baseStart_1348899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1348899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1348899 prefixEnd_1348899 := by exact prefixLift 1348899
  have htrace : WordTrace (prefixWord ++ tailWord_1348899) baseStart_1348899 baseEnd_1348899 := by
    simpa [prefixWord, tailWord_1348899, baseEnd_1348899] using wordTrace_append hprefix tailTrace_1348899
  have hstable : (prefixWord ++ tailWord_1348899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348899).length < 2 ^ (prefixWord ++ tailWord_1348899).sum := by decide
  have hdescent : baseEnd_1348899 < baseStart_1348899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348912 : List Nat := [2, 1, 1, 1, 2, 2, 5, 1, 4, 3]
def baseStart_1348912 : Nat := 118140960795 + 1348912 * 2 ^ 59
def prefixEnd_1348912 : Nat := 4983230072969 + 3 ^ 40 * 1348912 * 2
def baseEnd_1348912 : Nat := 461760144411821072864315

theorem tailTrace_1348912 : CollatzResearch.WordTrace tailWord_1348912 prefixEnd_1348912 461760144411821072864315 := by
  unfold tailWord_1348912
  simp only [CollatzResearch.WordTrace]
  refine ⟨24599431244564837336776495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32799241659419783115701993 24599431244564837336776495)
  ·
    refine ⟨36899146866847256005164743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24599431244564837336776495 36899146866847256005164743)
    ·
      refine ⟨55348720300270884007747115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36899146866847256005164743 55348720300270884007747115)
      ·
        refine ⟨83023080450406326011620673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55348720300270884007747115 83023080450406326011620673)
        ·
          refine ⟨62267310337804744508715505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83023080450406326011620673 62267310337804744508715505)
          ·
            refine ⟨46700482753353558381536629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62267310337804744508715505 46700482753353558381536629)
            ·
              refine ⟨4378170258126896098269059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46700482753353558381536629 4378170258126896098269059)
              ·
                refine ⟨6567255387190344147403589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4378170258126896098269059 6567255387190344147403589)
                ·
                  refine ⟨1231360385098189527638173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6567255387190344147403589 1231360385098189527638173)
                  ·
                    refine ⟨461760144411821072864315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1231360385098189527638173 461760144411821072864315)
                    ·
                      rfl

theorem cell22_1348912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 4, 3].length) (baseStart_1348912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1348912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1348912 prefixEnd_1348912 := by exact prefixLift 1348912
  have htrace : WordTrace (prefixWord ++ tailWord_1348912) baseStart_1348912 baseEnd_1348912 := by
    simpa [prefixWord, tailWord_1348912, baseEnd_1348912] using wordTrace_append hprefix tailTrace_1348912
  have hstable : (prefixWord ++ tailWord_1348912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348912).length < 2 ^ (prefixWord ++ tailWord_1348912).sum := by decide
  have hdescent : baseEnd_1348912 < baseStart_1348912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348914 : List Nat := [3, 2, 1, 1, 4, 1, 2, 4, 4]
def baseStart_1348914 : Nat := 118140960795 + 1348914 * 2 ^ 59
def prefixEnd_1348914 : Nat := 4983230072969 + 3 ^ 40 * 1348914 * 2
def baseEnd_1348914 : Nat := 153920276350897911438103

theorem tailTrace_1348914 : CollatzResearch.WordTrace tailWord_1348914 prefixEnd_1348914 153920276350897911438103 := by
  unfold tailWord_1348914
  simp only [CollatzResearch.WordTrace]
  refine ⟨12299733858780607253781449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32799290290081619343417197 12299733858780607253781449)
  ·
    refine ⟨9224800394085455440336087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12299733858780607253781449 9224800394085455440336087)
    ·
      refine ⟨13837200591128183160504131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9224800394085455440336087 13837200591128183160504131)
      ·
        refine ⟨20755800886692274740756197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13837200591128183160504131 20755800886692274740756197)
        ·
          refine ⟨3891712666254801513891787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20755800886692274740756197 3891712666254801513891787)
          ·
            refine ⟨5837568999382202270837681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3891712666254801513891787 5837568999382202270837681)
            ·
              refine ⟨4378176749536651703128261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5837568999382202270837681 4378176749536651703128261)
              ·
                refine ⟨820908140538122194336549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4378176749536651703128261 820908140538122194336549)
                ·
                  refine ⟨153920276350897911438103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 820908140538122194336549 153920276350897911438103)
                  ·
                    rfl

theorem cell22_1348914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 4, 4].length) (baseStart_1348914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1348914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1348914 prefixEnd_1348914 := by exact prefixLift 1348914
  have htrace : WordTrace (prefixWord ++ tailWord_1348914) baseStart_1348914 baseEnd_1348914 := by
    simpa [prefixWord, tailWord_1348914, baseEnd_1348914] using wordTrace_append hprefix tailTrace_1348914
  have hstable : (prefixWord ++ tailWord_1348914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348914).length < 2 ^ (prefixWord ++ tailWord_1348914).sum := by decide
  have hdescent : baseEnd_1348914 < baseStart_1348914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348929 : List Nat := [1, 2, 5, 2, 1, 1, 3, 1, 1, 5]
def baseStart_1348929 : Nat := 118140960795 + 1348929 * 2 ^ 59
def prefixEnd_1348929 : Nat := 4983230072969 + 3 ^ 40 * 1348929 * 2
def baseEnd_1348929 : Nat := 461765963859238695189263

theorem tailTrace_1348929 : CollatzResearch.WordTrace tailWord_1348929 prefixEnd_1348929 461765963859238695189263 := by
  unfold tailWord_1348929
  simp only [CollatzResearch.WordTrace]
  refine ⟨49199482530068086576921841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32799655020045391051281227 49199482530068086576921841)
  ·
    refine ⟨36899611897551064932691381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49199482530068086576921841 36899611897551064932691381)
    ·
      refine ⟨3459338615395412337439817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36899611897551064932691381 3459338615395412337439817)
      ·
        refine ⟨2594503961546559253079863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3459338615395412337439817 2594503961546559253079863)
        ·
          refine ⟨3891755942319838879619795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2594503961546559253079863 3891755942319838879619795)
          ·
            refine ⟨5837633913479758319429693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3891755942319838879619795 5837633913479758319429693)
            ·
              refine ⟨2189112717554909369786135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5837633913479758319429693 2189112717554909369786135)
              ·
                refine ⟨3283669076332364054679203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2189112717554909369786135 3283669076332364054679203)
                ·
                  refine ⟨4925503614498546082018805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3283669076332364054679203 4925503614498546082018805)
                  ·
                    refine ⟨461765963859238695189263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4925503614498546082018805 461765963859238695189263)
                    ·
                      rfl

theorem cell22_1348929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_1348929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1348929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1348929 prefixEnd_1348929 := by exact prefixLift 1348929
  have htrace : WordTrace (prefixWord ++ tailWord_1348929) baseStart_1348929 baseEnd_1348929 := by
    simpa [prefixWord, tailWord_1348929, baseEnd_1348929] using wordTrace_append hprefix tailTrace_1348929
  have hstable : (prefixWord ++ tailWord_1348929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348929).length < 2 ^ (prefixWord ++ tailWord_1348929).sum := by decide
  have hdescent : baseEnd_1348929 < baseStart_1348929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348987 : List Nat := [1, 1, 1, 1, 1, 6, 3, 3, 5]
def baseStart_1348987 : Nat := 118140960795 + 1348987 * 2 ^ 59
def prefixEnd_1348987 : Nat := 4983230072969 + 3 ^ 40 * 1348987 * 2
def baseEnd_1348987 : Nat := 153928606148181959079695

theorem tailTrace_1348987 : CollatzResearch.WordTrace tailWord_1348987 prefixEnd_1348987 153928606148181959079695 := by
  unfold tailWord_1348987
  simp only [CollatzResearch.WordTrace]
  refine ⟨49201597963857962482533215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32801065309238641655022143 49201597963857962482533215)
  ·
    refine ⟨73802396945786943723799823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49201597963857962482533215 73802396945786943723799823)
    ·
      refine ⟨110703595418680415585699735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73802396945786943723799823 110703595418680415585699735)
      ·
        refine ⟨166055393128020623378549603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110703595418680415585699735 166055393128020623378549603)
        ·
          refine ⟨249083089692030935067824405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166055393128020623378549603 249083089692030935067824405)
          ·
            refine ⟨11675769829313950081304269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 249083089692030935067824405 11675769829313950081304269)
            ·
              refine ⟨4378413685992731280489101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11675769829313950081304269 4378413685992731280489101)
              ·
                refine ⟨1641905132247274230183413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4378413685992731280489101 1641905132247274230183413)
                ·
                  refine ⟨153928606148181959079695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1641905132247274230183413 153928606148181959079695)
                  ·
                    rfl

theorem cell22_1348987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 3, 5].length) (baseStart_1348987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1348987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1348987 prefixEnd_1348987 := by exact prefixLift 1348987
  have htrace : WordTrace (prefixWord ++ tailWord_1348987) baseStart_1348987 baseEnd_1348987 := by
    simpa [prefixWord, tailWord_1348987, baseEnd_1348987] using wordTrace_append hprefix tailTrace_1348987
  have hstable : (prefixWord ++ tailWord_1348987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348987).length < 2 ^ (prefixWord ++ tailWord_1348987).sum := by decide
  have hdescent : baseEnd_1348987 < baseStart_1348987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349049 : List Nat := [1, 2, 1, 4, 4, 1, 1, 2, 6]
def baseStart_1349049 : Nat := 118140960795 + 1349049 * 2 ^ 59
def prefixEnd_1349049 : Nat := 4983230072969 + 3 ^ 40 * 1349049 * 2
def baseEnd_1349049 : Nat := 153935680770532794062965

theorem tailTrace_1349049 : CollatzResearch.WordTrace tailWord_1349049 prefixEnd_1349049 153935680770532794062965 := by
  unfold tailWord_1349049
  simp only [CollatzResearch.WordTrace]
  refine ⟨49203859289633347071290201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32802572859755564714193467 49203859289633347071290201)
  ·
    refine ⟨36902894467225010303467651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49203859289633347071290201 36902894467225010303467651)
    ·
      refine ⟨55354341700837515455201477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36902894467225010303467651 55354341700837515455201477)
      ·
        refine ⟨10378939068907034147850277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55354341700837515455201477 10378939068907034147850277)
        ·
          refine ⟨1946051075420068902721927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10378939068907034147850277 1946051075420068902721927)
          ·
            refine ⟨2919076613130103354082891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1946051075420068902721927 2919076613130103354082891)
            ·
              refine ⟨4378614919695155031124337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2919076613130103354082891 4378614919695155031124337)
              ·
                refine ⟨3283961189771366273343253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4378614919695155031124337 3283961189771366273343253)
                ·
                  refine ⟨153935680770532794062965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3283961189771366273343253 153935680770532794062965)
                  ·
                    rfl

theorem cell22_1349049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 2, 6].length) (baseStart_1349049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1349049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1349049 prefixEnd_1349049 := by exact prefixLift 1349049
  have htrace : WordTrace (prefixWord ++ tailWord_1349049) baseStart_1349049 baseEnd_1349049 := by
    simpa [prefixWord, tailWord_1349049, baseEnd_1349049] using wordTrace_append hprefix tailTrace_1349049
  have hstable : (prefixWord ++ tailWord_1349049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349049).length < 2 ^ (prefixWord ++ tailWord_1349049).sum := by decide
  have hdescent : baseEnd_1349049 < baseStart_1349049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349064 : List Nat := [2, 1, 3, 1, 3, 1, 2, 2, 4, 3]
def baseStart_1349064 : Nat := 118140960795 + 1349064 * 2 ^ 59
def prefixEnd_1349064 : Nat := 4983230072969 + 3 ^ 40 * 1349064 * 2
def baseEnd_1349064 : Nat := 461812177118143343063849

theorem tailTrace_1349064 : CollatzResearch.WordTrace tailWord_1349064 prefixEnd_1349064 461812177118143343063849 := by
  unfold tailWord_1349064
  simp only [CollatzResearch.WordTrace]
  refine ⟨24602203192289502316543123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32802937589719336422057497 24602203192289502316543123)
  ·
    refine ⟨36903304788434253474814685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24602203192289502316543123 36903304788434253474814685)
    ·
      refine ⟨13838739295662845053055507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36903304788434253474814685 13838739295662845053055507)
      ·
        refine ⟨20758108943494267579583261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13838739295662845053055507 20758108943494267579583261)
        ·
          refine ⟨7784290853810350342343723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20758108943494267579583261 7784290853810350342343723)
          ·
            refine ⟨11676436280715525513515585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7784290853810350342343723 11676436280715525513515585)
            ·
              refine ⟨8757327210536644135136689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11676436280715525513515585 8757327210536644135136689)
              ·
                refine ⟨6567995407902483101352517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8757327210536644135136689 6567995407902483101352517)
                ·
                  refine ⟨1231499138981715581503597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6567995407902483101352517 1231499138981715581503597)
                  ·
                    refine ⟨461812177118143343063849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1231499138981715581503597 461812177118143343063849)
                    ·
                      rfl

theorem cell22_1349064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 4, 3].length) (baseStart_1349064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1349064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1349064 prefixEnd_1349064 := by exact prefixLift 1349064
  have htrace : WordTrace (prefixWord ++ tailWord_1349064) baseStart_1349064 baseEnd_1349064 := by
    simpa [prefixWord, tailWord_1349064, baseEnd_1349064] using wordTrace_append hprefix tailTrace_1349064
  have hstable : (prefixWord ++ tailWord_1349064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349064).length < 2 ^ (prefixWord ++ tailWord_1349064).sum := by decide
  have hdescent : baseEnd_1349064 < baseStart_1349064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349066 : List Nat := [3, 1, 2, 1, 2, 4, 2, 3, 4]
def baseStart_1349066 : Nat := 118140960795 + 1349066 * 2 ^ 59
def prefixEnd_1349066 : Nat := 4983230072969 + 3 ^ 40 * 1349066 * 2
def baseEnd_1349066 : Nat := 153937620586338668171281

theorem tailTrace_1349066 : CollatzResearch.WordTrace tailWord_1349066 prefixEnd_1349066 153937620586338668171281 := by
  unfold tailWord_1349066
  simp only [CollatzResearch.WordTrace]
  refine ⟨12301119832642939743664763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32802986220381172649772701 12301119832642939743664763)
  ·
    refine ⟨18451679748964409615497145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12301119832642939743664763 18451679748964409615497145)
    ·
      refine ⟨13838759811723307211622859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18451679748964409615497145 13838759811723307211622859)
      ·
        refine ⟨20758139717584960817434289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13838759811723307211622859 20758139717584960817434289)
        ·
          refine ⟨15568604788188720613075717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20758139717584960817434289 15568604788188720613075717)
          ·
            refine ⟨2919113397785385114951697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15568604788188720613075717 2919113397785385114951697)
            ·
              refine ⟨2189335048339038836213773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2919113397785385114951697 2189335048339038836213773)
              ·
                refine ⟨821000643127139563580165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2189335048339038836213773 821000643127139563580165)
                ·
                  refine ⟨153937620586338668171281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 821000643127139563580165 153937620586338668171281)
                  ·
                    rfl

theorem cell22_1349066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 3, 4].length) (baseStart_1349066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1349066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1349066 prefixEnd_1349066 := by exact prefixLift 1349066
  have htrace : WordTrace (prefixWord ++ tailWord_1349066) baseStart_1349066 baseEnd_1349066 := by
    simpa [prefixWord, tailWord_1349066, baseEnd_1349066] using wordTrace_append hprefix tailTrace_1349066
  have hstable : (prefixWord ++ tailWord_1349066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349066).length < 2 ^ (prefixWord ++ tailWord_1349066).sum := by decide
  have hdescent : baseEnd_1349066 < baseStart_1349066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349068 : List Nat := [2, 2, 1, 4, 2, 3, 2, 1, 1, 4]
def baseStart_1349068 : Nat := 118140960795 + 1349068 * 2 ^ 59
def prefixEnd_1349068 : Nat := 4983230072969 + 3 ^ 40 * 1349068 * 2
def baseEnd_1349068 : Nat := 461813546399888665963837

theorem tailTrace_1349068 : CollatzResearch.WordTrace tailWord_1349068 prefixEnd_1349068 461813546399888665963837 := by
  unfold tailWord_1349068
  simp only [CollatzResearch.WordTrace]
  refine ⟨24602276138282256658115929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32803034851043008877487905 24602276138282256658115929)
  ·
    refine ⟨18451707103711692493586947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24602276138282256658115929 18451707103711692493586947)
    ·
      refine ⟨27677560655567538740380421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18451707103711692493586947 27677560655567538740380421)
      ·
        refine ⟨5189542622918913513821329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27677560655567538740380421 5189542622918913513821329)
        ·
          refine ⟨3892156967189185135365997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5189542622918913513821329 3892156967189185135365997)
          ·
            refine ⟨1459558862695944425762249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3892156967189185135365997 1459558862695944425762249)
            ·
              refine ⟨1094669147021958319321687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1459558862695944425762249 1094669147021958319321687)
              ·
                refine ⟨1642003720532937478982531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1094669147021958319321687 1642003720532937478982531)
                ·
                  refine ⟨2463005580799406218473797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1642003720532937478982531 2463005580799406218473797)
                  ·
                    refine ⟨461813546399888665963837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2463005580799406218473797 461813546399888665963837)
                    ·
                      rfl

theorem cell22_1349068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2, 1, 1, 4].length) (baseStart_1349068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1349068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1349068 prefixEnd_1349068 := by exact prefixLift 1349068
  have htrace : WordTrace (prefixWord ++ tailWord_1349068) baseStart_1349068 baseEnd_1349068 := by
    simpa [prefixWord, tailWord_1349068, baseEnd_1349068] using wordTrace_append hprefix tailTrace_1349068
  have hstable : (prefixWord ++ tailWord_1349068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349068).length < 2 ^ (prefixWord ++ tailWord_1349068).sum := by decide
  have hdescent : baseEnd_1349068 < baseStart_1349068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349077 : List Nat := [1, 3, 2, 3, 1, 1, 11]
def baseStart_1349077 : Nat := 118140960795 + 1349077 * 2 ^ 59
def prefixEnd_1349077 : Nat := 4983230072969 + 3 ^ 40 * 1349077 * 2
def baseEnd_1349077 : Nat := 17104319529030208981067

theorem tailTrace_1349077 : CollatzResearch.WordTrace tailWord_1349077 prefixEnd_1349077 17104319529030208981067 := by
  unfold tailWord_1349077
  simp only [CollatzResearch.WordTrace]
  refine ⟨49204880533531907853309485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32803253689021271902206323 49204880533531907853309485)
  ·
    refine ⟨18451830200074465444991057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49204880533531907853309485 18451830200074465444991057)
    ·
      refine ⟨13838872650055849083743293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18451830200074465444991057 13838872650055849083743293)
      ·
        refine ⟨5189577243770943406403735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13838872650055849083743293 5189577243770943406403735)
        ·
          refine ⟨7784365865656415109605603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5189577243770943406403735 7784365865656415109605603)
          ·
            refine ⟨11676548798484622664408405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7784365865656415109605603 11676548798484622664408405)
            ·
              refine ⟨17104319529030208981067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 11676548798484622664408405 17104319529030208981067)
              ·
                rfl

theorem cell22_1349077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 11].length) (baseStart_1349077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1349077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1349077 prefixEnd_1349077 := by exact prefixLift 1349077
  have htrace : WordTrace (prefixWord ++ tailWord_1349077) baseStart_1349077 baseEnd_1349077 := by
    simpa [prefixWord, tailWord_1349077, baseEnd_1349077] using wordTrace_append hprefix tailTrace_1349077
  have hstable : (prefixWord ++ tailWord_1349077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349077).length < 2 ^ (prefixWord ++ tailWord_1349077).sum := by decide
  have hdescent : baseEnd_1349077 < baseStart_1349077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349081 : List Nat := [1, 2, 1, 2, 4, 2, 3, 2, 2, 3]
def baseStart_1349081 : Nat := 118140960795 + 1349081 * 2 ^ 59
def prefixEnd_1349081 : Nat := 4983230072969 + 3 ^ 40 * 1349081 * 2
def baseEnd_1349081 : Nat := 461817996565560965388797

theorem tailTrace_1349081 : CollatzResearch.WordTrace tailWord_1349081 prefixEnd_1349081 461817996565560965388797 := by
  unfold tailWord_1349081
  simp only [CollatzResearch.WordTrace]
  refine ⟨49205026425517416536455097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32803350950344944357636731 49205026425517416536455097)
  ·
    refine ⟨36903769819138062402341323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49205026425517416536455097 36903769819138062402341323)
    ·
      refine ⟨55355654728707093603511985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36903769819138062402341323 55355654728707093603511985)
      ·
        refine ⟨41516741046530320202633989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55355654728707093603511985 41516741046530320202633989)
        ·
          refine ⟨7784388946224435037993873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41516741046530320202633989 7784388946224435037993873)
          ·
            refine ⟨5838291709668326278495405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7784388946224435037993873 5838291709668326278495405)
            ·
              refine ⟨2189359391125622354435777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5838291709668326278495405 2189359391125622354435777)
              ·
                refine ⟨1642019543344216765826833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2189359391125622354435777 1642019543344216765826833)
                ·
                  refine ⟨1231514657508162574370125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1642019543344216765826833 1231514657508162574370125)
                  ·
                    refine ⟨461817996565560965388797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1231514657508162574370125 461817996565560965388797)
                    ·
                      rfl

theorem cell22_1349081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 2, 2, 3].length) (baseStart_1349081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1349081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1349081 prefixEnd_1349081 := by exact prefixLift 1349081
  have htrace : WordTrace (prefixWord ++ tailWord_1349081) baseStart_1349081 baseEnd_1349081 := by
    simpa [prefixWord, tailWord_1349081, baseEnd_1349081] using wordTrace_append hprefix tailTrace_1349081
  have hstable : (prefixWord ++ tailWord_1349081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349081).length < 2 ^ (prefixWord ++ tailWord_1349081).sum := by decide
  have hdescent : baseEnd_1349081 < baseStart_1349081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349098 : List Nat := [3, 1, 3, 1, 5, 1, 1, 1, 1, 5]
def baseStart_1349098 : Nat := 118140960795 + 1349098 * 2 ^ 59
def prefixEnd_1349098 : Nat := 4983230072969 + 3 ^ 40 * 1349098 * 2
def baseEnd_1349098 : Nat := 461823816012978587713745

theorem tailTrace_1349098 : CollatzResearch.WordTrace tailWord_1349098 prefixEnd_1349098 461823816012978587713745 := by
  unfold tailWord_1349098
  simp only [CollatzResearch.WordTrace]
  refine ⟨12301411616613957109955987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32803764310970552293215965 12301411616613957109955987)
  ·
    refine ⟨18452117424920935664933981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12301411616613957109955987 18452117424920935664933981)
    ·
      refine ⟨6919544034345350874350243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18452117424920935664933981 6919544034345350874350243)
      ·
        refine ⟨10379316051518026311525365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6919544034345350874350243 10379316051518026311525365)
        ·
          refine ⟨973060879829814966705503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10379316051518026311525365 973060879829814966705503)
          ·
            refine ⟨1459591319744722450058255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 973060879829814966705503 1459591319744722450058255)
            ·
              refine ⟨2189386979617083675087383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1459591319744722450058255 2189386979617083675087383)
              ·
                refine ⟨3284080469425625512631075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2189386979617083675087383 3284080469425625512631075)
                ·
                  refine ⟨4926120704138438268946613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3284080469425625512631075 4926120704138438268946613)
                  ·
                    refine ⟨461823816012978587713745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4926120704138438268946613 461823816012978587713745)
                    ·
                      rfl

theorem cell22_1349098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 1, 1, 5].length) (baseStart_1349098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1349098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1349098 prefixEnd_1349098 := by exact prefixLift 1349098
  have htrace : WordTrace (prefixWord ++ tailWord_1349098) baseStart_1349098 baseEnd_1349098 := by
    simpa [prefixWord, tailWord_1349098, baseEnd_1349098] using wordTrace_append hprefix tailTrace_1349098
  have hstable : (prefixWord ++ tailWord_1349098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349098).length < 2 ^ (prefixWord ++ tailWord_1349098).sum := by decide
  have hdescent : baseEnd_1349098 < baseStart_1349098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349154 : List Nat := [3, 3, 1, 1, 1, 1, 2, 3, 2, 5]
def baseStart_1349154 : Nat := 118140960795 + 1349154 * 2 ^ 59
def prefixEnd_1349154 : Nat := 4983230072969 + 3 ^ 40 * 1349154 * 2
def baseEnd_1349154 : Nat := 461842985957413108313573

theorem tailTrace_1349154 : CollatzResearch.WordTrace tailWord_1349154 prefixEnd_1349154 461842985957413108313573 := by
  unfold tailWord_1349154
  simp only [CollatzResearch.WordTrace]
  refine ⟨12301922238563237500965629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32805125969501966669241677 12301922238563237500965629)
  ·
    refine ⟨4613220839461214062862111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12301922238563237500965629 4613220839461214062862111)
    ·
      refine ⟨6919831259191821094293167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4613220839461214062862111 6919831259191821094293167)
      ·
        refine ⟨10379746888787731641439751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6919831259191821094293167 10379746888787731641439751)
        ·
          refine ⟨15569620333181597462159627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10379746888787731641439751 15569620333181597462159627)
          ·
            refine ⟨23354430499772396193239441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15569620333181597462159627 23354430499772396193239441)
            ·
              refine ⟨17515822874829297144929581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23354430499772396193239441 17515822874829297144929581)
              ·
                refine ⟨6568433578060986429348593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17515822874829297144929581 6568433578060986429348593)
                ·
                  refine ⟨4926325183545739822011445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6568433578060986429348593 4926325183545739822011445)
                  ·
                    refine ⟨461842985957413108313573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4926325183545739822011445 461842985957413108313573)
                    ·
                      rfl

theorem cell22_1349154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_1349154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1349154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1349154 prefixEnd_1349154 := by exact prefixLift 1349154
  have htrace : WordTrace (prefixWord ++ tailWord_1349154) baseStart_1349154 baseEnd_1349154 := by
    simpa [prefixWord, tailWord_1349154, baseEnd_1349154] using wordTrace_append hprefix tailTrace_1349154
  have hstable : (prefixWord ++ tailWord_1349154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349154).length < 2 ^ (prefixWord ++ tailWord_1349154).sum := by decide
  have hdescent : baseEnd_1349154 < baseStart_1349154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349190 : List Nat := [6, 1, 1, 1, 3, 1, 2, 2, 5]
def baseStart_1349190 : Nat := 118140960795 + 1349190 * 2 ^ 59
def prefixEnd_1349190 : Nat := 4983230072969 + 3 ^ 40 * 1349190 * 2
def baseEnd_1349190 : Nat := 153951769831040338137821

theorem tailTrace_1349190 : CollatzResearch.WordTrace tailWord_1349190 prefixEnd_1349190 153951769831040338137821 := by
  unfold tailWord_1349190
  simp only [CollatzResearch.WordTrace]
  refine ⟨1537781311941329004755407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 32806001321415018768115349 1537781311941329004755407)
  ·
    refine ⟨2306671967911993507133111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1537781311941329004755407 2306671967911993507133111)
    ·
      refine ⟨3460007951867990260699667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2306671967911993507133111 3460007951867990260699667)
      ·
        refine ⟨5190011927801985391049501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3460007951867990260699667 5190011927801985391049501)
        ·
          refine ⟨1946254472925744521643563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5190011927801985391049501 1946254472925744521643563)
          ·
            refine ⟨2919381709388616782465345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1946254472925744521643563 2919381709388616782465345)
            ·
              refine ⟨2189536282041462586849009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2919381709388616782465345 2189536282041462586849009)
              ·
                refine ⟨1642152211531096940136757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2189536282041462586849009 1642152211531096940136757)
                ·
                  refine ⟨153951769831040338137821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1642152211531096940136757 153951769831040338137821)
                  ·
                    rfl

theorem cell22_1349190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_1349190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1349190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1349190 prefixEnd_1349190 := by exact prefixLift 1349190
  have htrace : WordTrace (prefixWord ++ tailWord_1349190) baseStart_1349190 baseEnd_1349190 := by
    simpa [prefixWord, tailWord_1349190, baseEnd_1349190] using wordTrace_append hprefix tailTrace_1349190
  have hstable : (prefixWord ++ tailWord_1349190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349190).length < 2 ^ (prefixWord ++ tailWord_1349190).sum := by decide
  have hdescent : baseEnd_1349190 < baseStart_1349190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349201 : List Nat := [1, 2, 2, 1, 3, 2, 3, 4, 4]
def baseStart_1349201 : Nat := 118140960795 + 1349201 * 2 ^ 59
def prefixEnd_1349201 : Nat := 4983230072969 + 3 ^ 40 * 1349201 * 2
def baseEnd_1349201 : Nat := 153953025005973550796143

theorem tailTrace_1349201 : CollatzResearch.WordTrace tailWord_1349201 prefixEnd_1349201 153953025005973550796143 := by
  unfold tailWord_1349201
  simp only [CollatzResearch.WordTrace]
  refine ⟨49209403185082677030823457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32806268790055118020548971 49209403185082677030823457)
  ·
    refine ⟨36907052388812007773117593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49209403185082677030823457 36907052388812007773117593)
    ·
      refine ⟨27680289291609005829838195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36907052388812007773117593 27680289291609005829838195)
      ·
        refine ⟨41520433937413508744757293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27680289291609005829838195 41520433937413508744757293)
        ·
          refine ⟨15570162726530065779283985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41520433937413508744757293 15570162726530065779283985)
          ·
            refine ⟨11677622044897549334462989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15570162726530065779283985 11677622044897549334462989)
            ·
              refine ⟨4379108266836581000423621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11677622044897549334462989 4379108266836581000423621)
              ·
                refine ⟨821082800031858937579429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4379108266836581000423621 821082800031858937579429)
                ·
                  refine ⟨153953025005973550796143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 821082800031858937579429 153953025005973550796143)
                  ·
                    rfl

theorem cell22_1349201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 4, 4].length) (baseStart_1349201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1349201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1349201 prefixEnd_1349201 := by exact prefixLift 1349201
  have htrace : WordTrace (prefixWord ++ tailWord_1349201) baseStart_1349201 baseEnd_1349201 := by
    simpa [prefixWord, tailWord_1349201, baseEnd_1349201] using wordTrace_append hprefix tailTrace_1349201
  have hstable : (prefixWord ++ tailWord_1349201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349201).length < 2 ^ (prefixWord ++ tailWord_1349201).sum := by decide
  have hdescent : baseEnd_1349201 < baseStart_1349201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349325 : List Nat := [1, 6, 2, 1, 1, 2, 1, 3, 5]
def baseStart_1349325 : Nat := 118140960795 + 1349325 * 2 ^ 59
def prefixEnd_1349325 : Nat := 4983230072969 + 3 ^ 40 * 1349325 * 2
def baseEnd_1349325 : Nat := 153967174250675220762683

theorem tailTrace_1349325 : CollatzResearch.WordTrace tailWord_1349325 prefixEnd_1349325 153967174250675220762683 := by
  unfold tailWord_1349325
  simp only [CollatzResearch.WordTrace]
  refine ⟨49213925836633446208337429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32809283891088964138891619 49213925836633446208337429)
  ·
    refine ⟨2306902773592192791015817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 49213925836633446208337429 2306902773592192791015817)
    ·
      refine ⟨1730177080194144593261863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2306902773592192791015817 1730177080194144593261863)
      ·
        refine ⟨2595265620291216889892795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1730177080194144593261863 2595265620291216889892795)
        ·
          refine ⟨3892898430436825334839193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2595265620291216889892795 3892898430436825334839193)
          ·
            refine ⟨2919673822827619001129395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3892898430436825334839193 2919673822827619001129395)
            ·
              refine ⟨4379510734241428501694093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2919673822827619001129395 4379510734241428501694093)
              ·
                refine ⟨1642316525340535688135285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4379510734241428501694093 1642316525340535688135285)
                ·
                  refine ⟨153967174250675220762683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1642316525340535688135285 153967174250675220762683)
                  ·
                    rfl

theorem cell22_1349325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_1349325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1349325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1349325 prefixEnd_1349325 := by exact prefixLift 1349325
  have htrace : WordTrace (prefixWord ++ tailWord_1349325) baseStart_1349325 baseEnd_1349325 := by
    simpa [prefixWord, tailWord_1349325, baseEnd_1349325] using wordTrace_append hprefix tailTrace_1349325
  have hstable : (prefixWord ++ tailWord_1349325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349325).length < 2 ^ (prefixWord ++ tailWord_1349325).sum := by decide
  have hdescent : baseEnd_1349325 < baseStart_1349325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349338 : List Nat := [3, 1, 1, 2, 2, 3, 3, 2, 1, 4]
def baseStart_1349338 : Nat := 118140960795 + 1349338 * 2 ^ 59
def prefixEnd_1349338 : Nat := 4983230072969 + 3 ^ 40 * 1349338 * 2
def baseEnd_1349338 : Nat := 461905972917697961713009

theorem tailTrace_1349338 : CollatzResearch.WordTrace tailWord_1349338 prefixEnd_1349338 461905972917697961713009 := by
  unfold tailWord_1349338
  simp only [CollatzResearch.WordTrace]
  refine ⟨12303599996396587357140167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32809599990390899619040445 12303599996396587357140167)
  ·
    refine ⟨18455399994594881035710251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12303599996396587357140167 18455399994594881035710251)
    ·
      refine ⟨27683099991892321553565377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18455399994594881035710251 27683099991892321553565377)
      ·
        refine ⟨20762324993919241165174033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27683099991892321553565377 20762324993919241165174033)
        ·
          refine ⟨15571743745439430873880525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20762324993919241165174033 15571743745439430873880525)
          ·
            refine ⟨5839403904539786577705197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15571743745439430873880525 5839403904539786577705197)
            ·
              refine ⟨2189776464202419966639449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5839403904539786577705197 2189776464202419966639449)
              ·
                refine ⟨1642332348151814974979587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2189776464202419966639449 1642332348151814974979587)
                ·
                  refine ⟨2463498522227722462469381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1642332348151814974979587 2463498522227722462469381)
                  ·
                    refine ⟨461905972917697961713009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2463498522227722462469381 461905972917697961713009)
                    ·
                      rfl

theorem cell22_1349338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 2, 1, 4].length) (baseStart_1349338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1349338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1349338 prefixEnd_1349338 := by exact prefixLift 1349338
  have htrace : WordTrace (prefixWord ++ tailWord_1349338) baseStart_1349338 baseEnd_1349338 := by
    simpa [prefixWord, tailWord_1349338, baseEnd_1349338] using wordTrace_append hprefix tailTrace_1349338
  have hstable : (prefixWord ++ tailWord_1349338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349338).length < 2 ^ (prefixWord ++ tailWord_1349338).sum := by decide
  have hdescent : baseEnd_1349338 < baseStart_1349338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349406 : List Nat := [4, 3, 2, 2, 1, 2, 2, 1, 1, 4]
def baseStart_1349406 : Nat := 118140960795 + 1349406 * 2 ^ 59
def prefixEnd_1349406 : Nat := 4983230072969 + 3 ^ 40 * 1349406 * 2
def baseEnd_1349406 : Nat := 461929250707368451012801

theorem tailTrace_1349406 : CollatzResearch.WordTrace tailWord_1349406 prefixEnd_1349406 461929250707368451012801 := by
  unfold tailWord_1349406
  simp only [CollatzResearch.WordTrace]
  refine ⟨6152110018667499630254509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32811253432893331361357381 6152110018667499630254509)
  ·
    refine ⟨2307041257000312361345441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6152110018667499630254509 2307041257000312361345441)
    ·
      refine ⟨1730280942750234271009081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2307041257000312361345441 1730280942750234271009081)
      ·
        refine ⟨1297710707062675703256811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1730280942750234271009081 1297710707062675703256811)
        ·
          refine ⟨1946566060594013554885217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1297710707062675703256811 1946566060594013554885217)
          ·
            refine ⟨1459924545445510166163913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1946566060594013554885217 1459924545445510166163913)
            ·
              refine ⟨1094943409084132624622935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1459924545445510166163913 1094943409084132624622935)
              ·
                refine ⟨1642415113626198936934403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1094943409084132624622935 1642415113626198936934403)
                ·
                  refine ⟨2463622670439298405401605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1642415113626198936934403 2463622670439298405401605)
                  ·
                    refine ⟨461929250707368451012801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2463622670439298405401605 461929250707368451012801)
                    ·
                      rfl

theorem cell22_1349406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_1349406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1349406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1349406 prefixEnd_1349406 := by exact prefixLift 1349406
  have htrace : WordTrace (prefixWord ++ tailWord_1349406) baseStart_1349406 baseEnd_1349406 := by
    simpa [prefixWord, tailWord_1349406, baseEnd_1349406] using wordTrace_append hprefix tailTrace_1349406
  have hstable : (prefixWord ++ tailWord_1349406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349406).length < 2 ^ (prefixWord ++ tailWord_1349406).sum := by decide
  have hdescent : baseEnd_1349406 < baseStart_1349406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349473 : List Nat := [1, 2, 3, 1, 1, 1, 3, 5, 1, 4]
def baseStart_1349473 : Nat := 118140960795 + 1349473 * 2 ^ 59
def prefixEnd_1349473 : Nat := 4983230072969 + 3 ^ 40 * 1349473 * 2
def baseEnd_1349473 : Nat := 461952186176602609587595

theorem tailTrace_1349473 : CollatzResearch.WordTrace tailWord_1349473 prefixEnd_1349473 461952186176602609587595 := by
  unfold tailWord_1349473
  simp only [CollatzResearch.WordTrace]
  refine ⟨49219323840097267484725073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32812882560064844989816715 49219323840097267484725073)
  ·
    refine ⟨36914492880072950613543805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49219323840097267484725073 36914492880072950613543805)
    ·
      refine ⟨13842934830027356480078927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36914492880072950613543805 13842934830027356480078927)
      ·
        refine ⟨20764402245041034720118391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13842934830027356480078927 20764402245041034720118391)
        ·
          refine ⟨31146603367561552080177587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20764402245041034720118391 31146603367561552080177587)
          ·
            refine ⟨46719905051342328120266381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31146603367561552080177587 46719905051342328120266381)
            ·
              refine ⟨17519964394253373045099893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46719905051342328120266381 17519964394253373045099893)
              ·
                refine ⟨1642496661961253722978115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17519964394253373045099893 1642496661961253722978115)
                ·
                  refine ⟨2463744992941880584467173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1642496661961253722978115 2463744992941880584467173)
                  ·
                    refine ⟨461952186176602609587595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2463744992941880584467173 461952186176602609587595)
                    ·
                      rfl

theorem cell22_1349473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 5, 1, 4].length) (baseStart_1349473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1349473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1349473 prefixEnd_1349473 := by exact prefixLift 1349473
  have htrace : WordTrace (prefixWord ++ tailWord_1349473) baseStart_1349473 baseEnd_1349473 := by
    simpa [prefixWord, tailWord_1349473, baseEnd_1349473] using wordTrace_append hprefix tailTrace_1349473
  have hstable : (prefixWord ++ tailWord_1349473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349473).length < 2 ^ (prefixWord ++ tailWord_1349473).sum := by decide
  have hdescent : baseEnd_1349473 < baseStart_1349473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349494 : List Nat := [5, 1, 1, 3, 2, 2, 2, 1, 5]
def baseStart_1349494 : Nat := 118140960795 + 1349494 * 2 ^ 59
def prefixEnd_1349494 : Nat := 4983230072969 + 3 ^ 40 * 1349494 * 2
def baseEnd_1349494 : Nat := 153986458301921851604177

theorem tailTrace_1349494 : CollatzResearch.WordTrace tailWord_1349494 prefixEnd_1349494 153986458301921851604177 := by
  unfold tailWord_1349494
  simp only [CollatzResearch.WordTrace]
  refine ⟨3076255610813824254452471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32813393182014125380826357 3076255610813824254452471)
  ·
    refine ⟨4614383416220736381678707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3076255610813824254452471 4614383416220736381678707)
    ·
      refine ⟨6921575124331104572518061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4614383416220736381678707 6921575124331104572518061)
      ·
        refine ⟨2595590671624164214694273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6921575124331104572518061 2595590671624164214694273)
        ·
          refine ⟨1946693003718123161020705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2595590671624164214694273 1946693003718123161020705)
          ·
            refine ⟨1460019752788592370765529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1946693003718123161020705 1460019752788592370765529)
            ·
              refine ⟨1095014814591444278074147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1460019752788592370765529 1095014814591444278074147)
              ·
                refine ⟨1642522221887166417111221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1095014814591444278074147 1642522221887166417111221)
                ·
                  refine ⟨153986458301921851604177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1642522221887166417111221 153986458301921851604177)
                  ·
                    rfl

theorem cell22_1349494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_1349494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1349494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1349494 prefixEnd_1349494 := by exact prefixLift 1349494
  have htrace : WordTrace (prefixWord ++ tailWord_1349494) baseStart_1349494 baseEnd_1349494 := by
    simpa [prefixWord, tailWord_1349494, baseEnd_1349494] using wordTrace_append hprefix tailTrace_1349494
  have hstable : (prefixWord ++ tailWord_1349494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349494).length < 2 ^ (prefixWord ++ tailWord_1349494).sum := by decide
  have hdescent : baseEnd_1349494 < baseStart_1349494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
