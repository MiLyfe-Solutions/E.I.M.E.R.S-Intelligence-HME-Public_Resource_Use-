import V185TrunkScan23Chunk0314

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1862910 : List Nat := [4, 2, 2, 1, 1, 3, 1, 1, 4, 4]
def baseStart_1862910 : Nat := 118140960795 + 1862910 * 2 ^ 59
def prefixEnd_1862910 : Nat := 4983230072969 + 3 ^ 40 * 1862910 * 2
def baseEnd_1862910 : Nat := 318856082022470529919213

theorem tailTrace_1862910 : CollatzResearch.WordTrace tailWord_1862910 prefixEnd_1862910 318856082022470529919213 := by
  unfold tailWord_1862910
  simp only [CollatzResearch.WordTrace]
  refine ⟨8493238710125338067890273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45297273120668469695414789 8493238710125338067890273)
  ·
    refine ⟨6369929032594003550917705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8493238710125338067890273 6369929032594003550917705)
    ·
      refine ⟨4777446774445502663188279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6369929032594003550917705 4777446774445502663188279)
      ·
        refine ⟨7166170161668253994782419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4777446774445502663188279 7166170161668253994782419)
        ·
          refine ⟨10749255242502380992173629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7166170161668253994782419 10749255242502380992173629)
          ·
            refine ⟨4030970715938392872065111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10749255242502380992173629 4030970715938392872065111)
            ·
              refine ⟨6046456073907589308097667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4030970715938392872065111 6046456073907589308097667)
              ·
                refine ⟨9069684110861383962146501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6046456073907589308097667 9069684110861383962146501)
                ·
                  refine ⟨1700565770786509492902469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9069684110861383962146501 1700565770786509492902469)
                  ·
                    refine ⟨318856082022470529919213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1700565770786509492902469 318856082022470529919213)
                    ·
                      rfl

theorem cell23_1862910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_1862910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1862910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1862910 prefixEnd_1862910 := by exact prefixLift 1862910
  have htrace : WordTrace (prefixWord ++ tailWord_1862910) baseStart_1862910 baseEnd_1862910 := by
    simpa [prefixWord, tailWord_1862910, baseEnd_1862910] using wordTrace_append hprefix tailTrace_1862910
  have hstable : (prefixWord ++ tailWord_1862910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862910).length < 2 ^ (prefixWord ++ tailWord_1862910).sum := by decide
  have hdescent : baseEnd_1862910 < baseStart_1862910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862917 : List Nat := [1, 3, 1, 1, 2, 1, 3, 6, 1, 2, 2]
def baseStart_1862917 : Nat := 118140960795 + 1862917 * 2 ^ 59
def prefixEnd_1862917 : Nat := 4983230072969 + 3 ^ 40 * 1862917 * 2
def baseEnd_1862917 : Nat := 956571840431993062370107

theorem tailTrace_1862917 : CollatzResearch.WordTrace tailWord_1862917 prefixEnd_1862917 956571840431993062370107 := by
  unfold tailWord_1862917
  simp only [CollatzResearch.WordTrace]
  refine ⟨67946164991977344738627005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45297443327984896492418003 67946164991977344738627005)
  ·
    refine ⟨25479811871991504276985127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67946164991977344738627005 25479811871991504276985127)
    ·
      refine ⟨38219717807987256415477691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25479811871991504276985127 38219717807987256415477691)
      ·
        refine ⟨57329576711980884623216537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38219717807987256415477691 57329576711980884623216537)
        ·
          refine ⟨42997182533985663467412403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57329576711980884623216537 42997182533985663467412403)
          ·
            refine ⟨64495773800978495201118605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42997182533985663467412403 64495773800978495201118605)
            ·
              refine ⟨24185915175366935700419477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64495773800978495201118605 24185915175366935700419477)
              ·
                refine ⟨1133714773845325110957163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24185915175366935700419477 1133714773845325110957163)
                ·
                  refine ⟨1700572160767987666435745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1133714773845325110957163 1700572160767987666435745)
                  ·
                    refine ⟨1275429120575990749826809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1700572160767987666435745 1275429120575990749826809)
                    ·
                      refine ⟨956571840431993062370107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1275429120575990749826809 956571840431993062370107)
                      ·
                        rfl

theorem cell23_1862917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 6, 1, 2, 2].length) (baseStart_1862917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1862917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1862917 prefixEnd_1862917 := by exact prefixLift 1862917
  have htrace : WordTrace (prefixWord ++ tailWord_1862917) baseStart_1862917 baseEnd_1862917 := by
    simpa [prefixWord, tailWord_1862917, baseEnd_1862917] using wordTrace_append hprefix tailTrace_1862917
  have hstable : (prefixWord ++ tailWord_1862917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862917).length < 2 ^ (prefixWord ++ tailWord_1862917).sum := by decide
  have hdescent : baseEnd_1862917 < baseStart_1862917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862956 : List Nat := [2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 4]
def baseStart_1862956 : Nat := 118140960795 + 1862956 * 2 ^ 59
def prefixEnd_1862956 : Nat := 4983230072969 + 3 ^ 40 * 1862956 * 2
def baseEnd_1862956 : Nat := 956591866177518409782427

theorem tailTrace_1862956 : CollatzResearch.WordTrace tailWord_1862956 prefixEnd_1862956 956591866177518409782427 := by
  unfold tailWord_1862956
  simp only [CollatzResearch.WordTrace]
  refine ⟨33973793719418027199648361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45298391625890702932864481 33973793719418027199648361)
  ·
    refine ⟨25480345289563520399736271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33973793719418027199648361 25480345289563520399736271)
    ·
      refine ⟨38220517934345280599604407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25480345289563520399736271 38220517934345280599604407)
      ·
        refine ⟨57330776901517920899406611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38220517934345280599604407 57330776901517920899406611)
        ·
          refine ⟨85996165352276881349109917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57330776901517920899406611 85996165352276881349109917)
          ·
            refine ⟨32248562007103830505916219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85996165352276881349109917 32248562007103830505916219)
            ·
              refine ⟨48372843010655745758874329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32248562007103830505916219 48372843010655745758874329)
              ·
                refine ⟨36279632257991809319155747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48372843010655745758874329 36279632257991809319155747)
                ·
                  refine ⟨54419448386987713978733621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36279632257991809319155747 54419448386987713978733621)
                  ·
                    refine ⟨5101823286280098185506277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54419448386987713978733621 5101823286280098185506277)
                    ·
                      refine ⟨956591866177518409782427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5101823286280098185506277 956591866177518409782427)
                      ·
                        rfl

theorem cell23_1862956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 4].length) (baseStart_1862956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1862956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1862956 prefixEnd_1862956 := by exact prefixLift 1862956
  have htrace : WordTrace (prefixWord ++ tailWord_1862956) baseStart_1862956 baseEnd_1862956 := by
    simpa [prefixWord, tailWord_1862956, baseEnd_1862956] using wordTrace_append hprefix tailTrace_1862956
  have hstable : (prefixWord ++ tailWord_1862956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862956).length < 2 ^ (prefixWord ++ tailWord_1862956).sum := by decide
  have hdescent : baseEnd_1862956 < baseStart_1862956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862960 : List Nat := [2, 1, 1, 1, 2, 2, 3, 5, 1, 3, 2]
def baseStart_1862960 : Nat := 118140960795 + 1862960 * 2 ^ 59
def prefixEnd_1862960 : Nat := 4983230072969 + 3 ^ 40 * 1862960 * 2
def baseEnd_1862960 : Nat := 956593920100136394132409

theorem tailTrace_1862960 : CollatzResearch.WordTrace tailWord_1862960 prefixEnd_1862960 956593920100136394132409 := by
  unfold tailWord_1862960
  simp only [CollatzResearch.WordTrace]
  refine ⟨33973866665410781541221167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45298488887214375388294889 33973866665410781541221167)
  ·
    refine ⟨50960799998116172311831751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33973866665410781541221167 50960799998116172311831751)
    ·
      refine ⟨76441199997174258467747627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50960799998116172311831751 76441199997174258467747627)
      ·
        refine ⟨114661799995761387701621441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76441199997174258467747627 114661799995761387701621441)
        ·
          refine ⟨85996349996821040776216081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114661799995761387701621441 85996349996821040776216081)
          ·
            refine ⟨64497262497615780582162061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85996349996821040776216081 64497262497615780582162061)
            ·
              refine ⟨24186473436605917718310773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64497262497615780582162061 24186473436605917718310773)
              ·
                refine ⟨2267481884681804786091635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24186473436605917718310773 2267481884681804786091635)
                ·
                  refine ⟨3401222827022707179137453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2267481884681804786091635 3401222827022707179137453)
                  ·
                    refine ⟨1275458560133515192176545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3401222827022707179137453 1275458560133515192176545)
                    ·
                      refine ⟨956593920100136394132409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1275458560133515192176545 956593920100136394132409)
                      ·
                        rfl

theorem cell23_1862960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 5, 1, 3, 2].length) (baseStart_1862960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1862960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1862960 prefixEnd_1862960 := by exact prefixLift 1862960
  have htrace : WordTrace (prefixWord ++ tailWord_1862960) baseStart_1862960 baseEnd_1862960 := by
    simpa [prefixWord, tailWord_1862960, baseEnd_1862960] using wordTrace_append hprefix tailTrace_1862960
  have hstable : (prefixWord ++ tailWord_1862960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862960).length < 2 ^ (prefixWord ++ tailWord_1862960).sum := by decide
  have hdescent : baseEnd_1862960 < baseStart_1862960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862976 : List Nat := [2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 5]
def baseStart_1862976 : Nat := 118140960795 + 1862976 * 2 ^ 59
def prefixEnd_1862976 : Nat := 4983230072969 + 3 ^ 40 * 1862976 * 2
def baseEnd_1862976 : Nat := 956602135790608331532335

theorem tailTrace_1862976 : CollatzResearch.WordTrace tailWord_1862976 prefixEnd_1862976 956602135790608331532335 := by
  unfold tailWord_1862976
  simp only [CollatzResearch.WordTrace]
  refine ⟨33974158449381798907512391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45298877932509065210016521 33974158449381798907512391)
  ·
    refine ⟨50961237674072698361268587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33974158449381798907512391 50961237674072698361268587)
    ·
      refine ⟨76441856511109047541902881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50961237674072698361268587 76441856511109047541902881)
      ·
        refine ⟨57331392383331785656427161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76441856511109047541902881 57331392383331785656427161)
        ·
          refine ⟨42998544287498839242320371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57331392383331785656427161 42998544287498839242320371)
          ·
            refine ⟨64497816431248258863480557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42998544287498839242320371 64497816431248258863480557)
            ·
              refine ⟨24186681161718097073805209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64497816431248258863480557 24186681161718097073805209)
              ·
                refine ⟨18140010871288572805353907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24186681161718097073805209 18140010871288572805353907)
                ·
                  refine ⟨27210016306932859208030861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18140010871288572805353907 27210016306932859208030861)
                  ·
                    refine ⟨10203756115099822203011573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27210016306932859208030861 10203756115099822203011573)
                    ·
                      refine ⟨956602135790608331532335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10203756115099822203011573 956602135790608331532335)
                      ·
                        rfl

theorem cell23_1862976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 5].length) (baseStart_1862976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1862976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1862976 prefixEnd_1862976 := by exact prefixLift 1862976
  have htrace : WordTrace (prefixWord ++ tailWord_1862976) baseStart_1862976 baseEnd_1862976 := by
    simpa [prefixWord, tailWord_1862976, baseEnd_1862976] using wordTrace_append hprefix tailTrace_1862976
  have hstable : (prefixWord ++ tailWord_1862976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862976).length < 2 ^ (prefixWord ++ tailWord_1862976).sum := by decide
  have hdescent : baseEnd_1862976 < baseStart_1862976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862986 : List Nat := [3, 1, 2, 1, 1, 1, 1, 2, 2, 3, 6]
def baseStart_1862986 : Nat := 118140960795 + 1862986 * 2 ^ 59
def prefixEnd_1862986 : Nat := 4983230072969 + 3 ^ 40 * 1862986 * 2
def baseEnd_1862986 : Nat := 956607270597153292407289

theorem tailTrace_1862986 : CollatzResearch.WordTrace tailWord_1862986 prefixEnd_1862986 956607270597153292407289 := by
  unfold tailWord_1862986
  simp only [CollatzResearch.WordTrace]
  refine ⟨16987170407181842380722203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45299121085818246348592541 16987170407181842380722203)
  ·
    refine ⟨25480755610772763571083305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16987170407181842380722203 25480755610772763571083305)
    ·
      refine ⟨19110566708079572678312479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25480755610772763571083305 19110566708079572678312479)
      ·
        refine ⟨28665850062119359017468719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19110566708079572678312479 28665850062119359017468719)
        ·
          refine ⟨42998775093179038526203079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28665850062119359017468719 42998775093179038526203079)
          ·
            refine ⟨64498162639768557789304619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42998775093179038526203079 64498162639768557789304619)
            ·
              refine ⟨96747243959652836683956929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64498162639768557789304619 96747243959652836683956929)
              ·
                refine ⟨72560432969739627512967697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96747243959652836683956929 72560432969739627512967697)
                ·
                  refine ⟨54420324727304720634725773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72560432969739627512967697 54420324727304720634725773)
                  ·
                    refine ⟨20407621772739270238022165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54420324727304720634725773 20407621772739270238022165)
                    ·
                      refine ⟨956607270597153292407289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20407621772739270238022165 956607270597153292407289)
                      ·
                        rfl

theorem cell23_1862986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_1862986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1862986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1862986 prefixEnd_1862986 := by exact prefixLift 1862986
  have htrace : WordTrace (prefixWord ++ tailWord_1862986) baseStart_1862986 baseEnd_1862986 := by
    simpa [prefixWord, tailWord_1862986, baseEnd_1862986] using wordTrace_append hprefix tailTrace_1862986
  have hstable : (prefixWord ++ tailWord_1862986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862986).length < 2 ^ (prefixWord ++ tailWord_1862986).sum := by decide
  have hdescent : baseEnd_1862986 < baseStart_1862986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862990 : List Nat := [4, 1, 1, 1, 1, 1, 4, 3, 1, 4, 2]
def baseStart_1862990 : Nat := 118140960795 + 1862990 * 2 ^ 59
def prefixEnd_1862990 : Nat := 4983230072969 + 3 ^ 40 * 1862990 * 2
def baseEnd_1862990 : Nat := 956609324519771276757271

theorem tailTrace_1862990 : CollatzResearch.WordTrace tailWord_1862990 prefixEnd_1862990 956609324519771276757271 := by
  unfold tailWord_1862990
  simp only [CollatzResearch.WordTrace]
  refine ⟨8493603440089109775754303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45299218347141918804022949 8493603440089109775754303)
  ·
    refine ⟨12740405160133664663631455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8493603440089109775754303 12740405160133664663631455)
    ·
      refine ⟨19110607740200496995447183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12740405160133664663631455 19110607740200496995447183)
      ·
        refine ⟨28665911610300745493170775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19110607740200496995447183 28665911610300745493170775)
        ·
          refine ⟨42998867415451118239756163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28665911610300745493170775 42998867415451118239756163)
          ·
            refine ⟨64498301123176677359634245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42998867415451118239756163 64498301123176677359634245)
            ·
              refine ⟨12093431460595627004931421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64498301123176677359634245 12093431460595627004931421)
              ·
                refine ⟨4535036797723360126849283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12093431460595627004931421 4535036797723360126849283)
                ·
                  refine ⟨6802555196585040190273925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4535036797723360126849283 6802555196585040190273925)
                  ·
                    refine ⟨1275479099359695035676361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6802555196585040190273925 1275479099359695035676361)
                    ·
                      refine ⟨956609324519771276757271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1275479099359695035676361 956609324519771276757271)
                      ·
                        rfl

theorem cell23_1862990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 3, 1, 4, 2].length) (baseStart_1862990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1862990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1862990 prefixEnd_1862990 := by exact prefixLift 1862990
  have htrace : WordTrace (prefixWord ++ tailWord_1862990) baseStart_1862990 baseEnd_1862990 := by
    simpa [prefixWord, tailWord_1862990, baseEnd_1862990] using wordTrace_append hprefix tailTrace_1862990
  have hstable : (prefixWord ++ tailWord_1862990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862990).length < 2 ^ (prefixWord ++ tailWord_1862990).sum := by decide
  have hdescent : baseEnd_1862990 < baseStart_1862990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863023 : List Nat := [1, 1, 2, 1, 3, 1, 4, 2, 2, 3, 3]
def baseStart_1863023 : Nat := 118140960795 + 1863023 * 2 ^ 59
def prefixEnd_1863023 : Nat := 4983230072969 + 3 ^ 40 * 1863023 * 2
def baseEnd_1863023 : Nat := 956626269381369647644619

theorem tailTrace_1863023 : CollatzResearch.WordTrace tailWord_1863023 prefixEnd_1863023 956626269381369647644619 := by
  unfold tailWord_1863023
  simp only [CollatzResearch.WordTrace]
  refine ⟨67950031129593324841985723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45300020753062216561323815 67950031129593324841985723)
  ·
    refine ⟨101925046694389987262978585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67950031129593324841985723 101925046694389987262978585)
    ·
      refine ⟨76443785020792490447233939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101925046694389987262978585 76443785020792490447233939)
      ·
        refine ⟨114665677531188735670850909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76443785020792490447233939 114665677531188735670850909)
        ·
          refine ⟨42999629074195775876569091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114665677531188735670850909 42999629074195775876569091)
          ·
            refine ⟨64499443611293663814853637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42999629074195775876569091 64499443611293663814853637)
            ·
              refine ⟨12093645677117561965285057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64499443611293663814853637 12093645677117561965285057)
              ·
                refine ⟨9070234257838171473963793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12093645677117561965285057 9070234257838171473963793)
                ·
                  refine ⟨6802675693378628605472845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9070234257838171473963793 6802675693378628605472845)
                  ·
                    refine ⟨2551003385016985727052317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6802675693378628605472845 2551003385016985727052317)
                    ·
                      refine ⟨956626269381369647644619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2551003385016985727052317 956626269381369647644619)
                      ·
                        rfl

theorem cell23_1863023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 2, 3, 3].length) (baseStart_1863023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1863023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1863023 prefixEnd_1863023 := by exact prefixLift 1863023
  have htrace : WordTrace (prefixWord ++ tailWord_1863023) baseStart_1863023 baseEnd_1863023 := by
    simpa [prefixWord, tailWord_1863023, baseEnd_1863023] using wordTrace_append hprefix tailTrace_1863023
  have hstable : (prefixWord ++ tailWord_1863023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863023).length < 2 ^ (prefixWord ++ tailWord_1863023).sum := by decide
  have hdescent : baseEnd_1863023 < baseStart_1863023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863060 : List Nat := [2, 4, 2, 1, 2, 2, 1, 1, 1, 7]
def baseStart_1863060 : Nat := 118140960795 + 1863060 * 2 ^ 59
def prefixEnd_1863060 : Nat := 4983230072969 + 3 ^ 40 * 1863060 * 2
def baseEnd_1863060 : Nat := 318881756055195334293983

theorem tailTrace_1863060 : CollatzResearch.WordTrace tailWord_1863060 prefixEnd_1863060 318881756055195334293983 := by
  unfold tailWord_1863060
  simp only [CollatzResearch.WordTrace]
  refine ⟨33975690315229640080541317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45300920420306186774055089 33975690315229640080541317)
  ·
    refine ⟨6370441934105557515101497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33975690315229640080541317 6370441934105557515101497)
    ·
      refine ⟨4777831450579168136326123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6370441934105557515101497 4777831450579168136326123)
      ·
        refine ⟨7166747175868752204489185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4777831450579168136326123 7166747175868752204489185)
        ·
          refine ⟨5375060381901564153366889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7166747175868752204489185 5375060381901564153366889)
          ·
            refine ⟨4031295286426173115025167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5375060381901564153366889 4031295286426173115025167)
            ·
              refine ⟨6046942929639259672537751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4031295286426173115025167 6046942929639259672537751)
              ·
                refine ⟨9070414394458889508806627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6046942929639259672537751 9070414394458889508806627)
                ·
                  refine ⟨13605621591688334263209941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9070414394458889508806627 13605621591688334263209941)
                  ·
                    refine ⟨318881756055195334293983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13605621591688334263209941 318881756055195334293983)
                    ·
                      rfl

theorem cell23_1863060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_1863060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1863060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1863060 prefixEnd_1863060 := by exact prefixLift 1863060
  have htrace : WordTrace (prefixWord ++ tailWord_1863060) baseStart_1863060 baseEnd_1863060 := by
    simpa [prefixWord, tailWord_1863060, baseEnd_1863060] using wordTrace_append hprefix tailTrace_1863060
  have hstable : (prefixWord ++ tailWord_1863060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863060).length < 2 ^ (prefixWord ++ tailWord_1863060).sum := by decide
  have hdescent : baseEnd_1863060 < baseStart_1863060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863103 : List Nat := [1, 1, 2, 2, 2, 1, 1, 7, 6]
def baseStart_1863103 : Nat := 118140960795 + 1863103 * 2 ^ 59
def prefixEnd_1863103 : Nat := 4983230072969 + 3 ^ 40 * 1863103 * 2
def baseEnd_1863103 : Nat := 106296371981525481627139

theorem tailTrace_1863103 : CollatzResearch.WordTrace tailWord_1863103 prefixEnd_1863103 106296371981525481627139 := by
  unfold tailWord_1863103
  simp only [CollatzResearch.WordTrace]
  refine ⟨67952948969303498504897963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45301965979535665669931975 67952948969303498504897963)
  ·
    refine ⟨101929423453955247757346945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67952948969303498504897963 101929423453955247757346945)
    ·
      refine ⟨76447067590466435818010209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101929423453955247757346945 76447067590466435818010209)
      ·
        refine ⟨57335300692849826863507657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76447067590466435818010209 57335300692849826863507657)
        ·
          refine ⟨43001475519637370147630743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57335300692849826863507657 43001475519637370147630743)
          ·
            refine ⟨64502213279456055221446115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43001475519637370147630743 64502213279456055221446115)
            ·
              refine ⟨96753319919184082832169173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64502213279456055221446115 96753319919184082832169173)
              ·
                refine ⟨2267655935605876941378965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 96753319919184082832169173 2267655935605876941378965)
                ·
                  refine ⟨106296371981525481627139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2267655935605876941378965 106296371981525481627139)
                  ·
                    rfl

theorem cell23_1863103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 7, 6].length) (baseStart_1863103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1863103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1863103 prefixEnd_1863103 := by exact prefixLift 1863103
  have htrace : WordTrace (prefixWord ++ tailWord_1863103) baseStart_1863103 baseEnd_1863103 := by
    simpa [prefixWord, tailWord_1863103, baseEnd_1863103] using wordTrace_append hprefix tailTrace_1863103
  have hstable : (prefixWord ++ tailWord_1863103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863103).length < 2 ^ (prefixWord ++ tailWord_1863103).sum := by decide
  have hdescent : baseEnd_1863103 < baseStart_1863103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863113 : List Nat := [1, 2, 1, 1, 2, 1, 3, 1, 1, 7, 3]
def baseStart_1863113 : Nat := 118140960795 + 1863113 * 2 ^ 59
def prefixEnd_1863113 : Nat := 4983230072969 + 3 ^ 40 * 1863113 * 2
def baseEnd_1863113 : Nat := 956672482640274295519205

theorem tailTrace_1863113 : CollatzResearch.WordTrace tailWord_1863113 prefixEnd_1863113 956672482640274295519205 := by
  unfold tailWord_1863113
  simp only [CollatzResearch.WordTrace]
  refine ⟨67953313699267270212761993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45302209132844846808507995 67953313699267270212761993)
  ·
    refine ⟨50964985274450452659571495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67953313699267270212761993 50964985274450452659571495)
    ·
      refine ⟨76447477911675678989357243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50964985274450452659571495 76447477911675678989357243)
      ·
        refine ⟨114671216867513518484035865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76447477911675678989357243 114671216867513518484035865)
        ·
          refine ⟨86003412650635138863026899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114671216867513518484035865 86003412650635138863026899)
          ·
            refine ⟨129005118975952708294540349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86003412650635138863026899 129005118975952708294540349)
            ·
              refine ⟨48376919615982265610452631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129005118975952708294540349 48376919615982265610452631)
              ·
                refine ⟨72565379423973398415678947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48376919615982265610452631 72565379423973398415678947)
                ·
                  refine ⟨108848069135960097623518421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72565379423973398415678947 108848069135960097623518421)
                  ·
                    refine ⟨2551126620374064788051213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 108848069135960097623518421 2551126620374064788051213)
                    ·
                      refine ⟨956672482640274295519205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2551126620374064788051213 956672482640274295519205)
                      ·
                        rfl

theorem cell23_1863113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 7, 3].length) (baseStart_1863113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1863113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1863113 prefixEnd_1863113 := by exact prefixLift 1863113
  have htrace : WordTrace (prefixWord ++ tailWord_1863113) baseStart_1863113 baseEnd_1863113 := by
    simpa [prefixWord, tailWord_1863113, baseEnd_1863113] using wordTrace_append hprefix tailTrace_1863113
  have hstable : (prefixWord ++ tailWord_1863113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863113).length < 2 ^ (prefixWord ++ tailWord_1863113).sum := by decide
  have hdescent : baseEnd_1863113 < baseStart_1863113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863141 : List Nat := [1, 3, 1, 5, 1, 2, 3, 2, 1, 4]
def baseStart_1863141 : Nat := 118140960795 + 1863141 * 2 ^ 59
def prefixEnd_1863141 : Nat := 4983230072969 + 3 ^ 40 * 1863141 * 2
def baseEnd_1863141 : Nat := 318895620032866728656359

theorem tailTrace_1863141 : CollatzResearch.WordTrace tailWord_1863141 prefixEnd_1863141 318895620032866728656359 := by
  unfold tailWord_1863141
  simp only [CollatzResearch.WordTrace]
  refine ⟨67954334943165830994781277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45302889962110553996520851 67954334943165830994781277)
  ·
    refine ⟨25482875603687186623042979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67954334943165830994781277 25482875603687186623042979)
    ·
      refine ⟨38224313405530779934564469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25482875603687186623042979 38224313405530779934564469)
      ·
        refine ⟨3583529381768510618865419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38224313405530779934564469 3583529381768510618865419)
        ·
          refine ⟨5375294072652765928298129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3583529381768510618865419 5375294072652765928298129)
          ·
            refine ⟨4031470554489574446223597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5375294072652765928298129 4031470554489574446223597)
            ·
              refine ⟨1511801457933590417333849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4031470554489574446223597 1511801457933590417333849)
              ·
                refine ⟨1133851093450192813000387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1511801457933590417333849 1133851093450192813000387)
                ·
                  refine ⟨1700776640175289219500581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1133851093450192813000387 1700776640175289219500581)
                  ·
                    refine ⟨318895620032866728656359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1700776640175289219500581 318895620032866728656359)
                    ·
                      rfl

theorem cell23_1863141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3, 2, 1, 4].length) (baseStart_1863141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1863141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1863141 prefixEnd_1863141 := by exact prefixLift 1863141
  have htrace : WordTrace (prefixWord ++ tailWord_1863141) baseStart_1863141 baseEnd_1863141 := by
    simpa [prefixWord, tailWord_1863141, baseEnd_1863141] using wordTrace_append hprefix tailTrace_1863141
  have hstable : (prefixWord ++ tailWord_1863141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863141).length < 2 ^ (prefixWord ++ tailWord_1863141).sum := by decide
  have hdescent : baseEnd_1863141 < baseStart_1863141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863150 : List Nat := [4, 1, 2, 1, 2, 1, 2, 2, 3, 5]
def baseStart_1863150 : Nat := 118140960795 + 1863150 * 2 ^ 59
def prefixEnd_1863150 : Nat := 4983230072969 + 3 ^ 40 * 1863150 * 2
def baseEnd_1863150 : Nat := 318897160474830216918845

theorem tailTrace_1863150 : CollatzResearch.WordTrace tailWord_1863150 prefixEnd_1863150 318897160474830216918845 := by
  unfold tailWord_1863150
  simp only [CollatzResearch.WordTrace]
  refine ⟨8494332900016653191482363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45303108800088817021239269 8494332900016653191482363)
  ·
    refine ⟨12741499350024979787223545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8494332900016653191482363 12741499350024979787223545)
    ·
      refine ⟨9556124512518734840417659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12741499350024979787223545 9556124512518734840417659)
      ·
        refine ⟨14334186768778102260626489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9556124512518734840417659 14334186768778102260626489)
        ·
          refine ⟨10750640076583576695469867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14334186768778102260626489 10750640076583576695469867)
          ·
            refine ⟨16125960114875365043204801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10750640076583576695469867 16125960114875365043204801)
            ·
              refine ⟨12094470086156523782403601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16125960114875365043204801 12094470086156523782403601)
              ·
                refine ⟨9070852564617392836802701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12094470086156523782403601 9070852564617392836802701)
                ·
                  refine ⟨3401569711731522313801013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9070852564617392836802701 3401569711731522313801013)
                  ·
                    refine ⟨318897160474830216918845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3401569711731522313801013 318897160474830216918845)
                    ·
                      rfl

theorem cell23_1863150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_1863150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1863150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1863150 prefixEnd_1863150 := by exact prefixLift 1863150
  have htrace : WordTrace (prefixWord ++ tailWord_1863150) baseStart_1863150 baseEnd_1863150 := by
    simpa [prefixWord, tailWord_1863150, baseEnd_1863150] using wordTrace_append hprefix tailTrace_1863150
  have hstable : (prefixWord ++ tailWord_1863150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863150).length < 2 ^ (prefixWord ++ tailWord_1863150).sum := by decide
  have hdescent : baseEnd_1863150 < baseStart_1863150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863154 : List Nat := [3, 2, 1, 4, 1, 3, 2, 1, 6]
def baseStart_1863154 : Nat := 118140960795 + 1863154 * 2 ^ 59
def prefixEnd_1863154 : Nat := 4983230072969 + 3 ^ 40 * 1863154 * 2
def baseEnd_1863154 : Nat := 106299281705234292789613

theorem tailTrace_1863154 : CollatzResearch.WordTrace tailWord_1863154 prefixEnd_1863154 106299281705234292789613 := by
  unfold tailWord_1863154
  simp only [CollatzResearch.WordTrace]
  refine ⟨16988702273029683553751129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45303206061412489476669677 16988702273029683553751129)
  ·
    refine ⟨12741526704772262665313347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16988702273029683553751129 12741526704772262665313347)
    ·
      refine ⟨19112290057158393997970021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12741526704772262665313347 19112290057158393997970021)
      ·
        refine ⟨3583554385717198874619379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19112290057158393997970021 3583554385717198874619379)
        ·
          refine ⟨5375331578575798311929069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3583554385717198874619379 5375331578575798311929069)
          ·
            refine ⟨2015749341965924366973401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5375331578575798311929069 2015749341965924366973401)
            ·
              refine ⟨1511812006474443275230051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2015749341965924366973401 1511812006474443275230051)
              ·
                refine ⟨2267718009711664912845077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1511812006474443275230051 2267718009711664912845077)
                ·
                  refine ⟨106299281705234292789613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2267718009711664912845077 106299281705234292789613)
                  ·
                    rfl

theorem cell23_1863154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2, 1, 6].length) (baseStart_1863154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1863154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1863154 prefixEnd_1863154 := by exact prefixLift 1863154
  have htrace : WordTrace (prefixWord ++ tailWord_1863154) baseStart_1863154 baseEnd_1863154 := by
    simpa [prefixWord, tailWord_1863154, baseEnd_1863154] using wordTrace_append hprefix tailTrace_1863154
  have hstable : (prefixWord ++ tailWord_1863154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863154).length < 2 ^ (prefixWord ++ tailWord_1863154).sum := by decide
  have hdescent : baseEnd_1863154 < baseStart_1863154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863183 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 2, 6, 4]
def baseStart_1863183 : Nat := 118140960795 + 1863183 * 2 ^ 59
def prefixEnd_1863183 : Nat := 4983230072969 + 3 ^ 40 * 1863183 * 2
def baseEnd_1863183 : Nat := 956708426286089021643883

theorem tailTrace_1863183 : CollatzResearch.WordTrace tailWord_1863183 prefixEnd_1863183 956708426286089021643883 := by
  unfold tailWord_1863183
  simp only [CollatzResearch.WordTrace]
  refine ⟨67955866809013672167810203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45303911206009114778540135 67955866809013672167810203)
  ·
    refine ⟨101933800213520508251715305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67955866809013672167810203 101933800213520508251715305)
    ·
      refine ⟨76450350160140381188786479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101933800213520508251715305 76450350160140381188786479)
      ·
        refine ⟨114675525240210571783179719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76450350160140381188786479 114675525240210571783179719)
        ·
          refine ⟨172013287860315857674769579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114675525240210571783179719 172013287860315857674769579)
          ·
            refine ⟨258019931790473786512154369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172013287860315857674769579 258019931790473786512154369)
            ·
              refine ⟨193514948842855339884115777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 258019931790473786512154369 193514948842855339884115777)
              ·
                refine ⟨145136211632141504913086833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193514948842855339884115777 145136211632141504913086833)
                ·
                  refine ⟨108852158724106128684815125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145136211632141504913086833 108852158724106128684815125)
                  ·
                    refine ⟨5102444940192474782100709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 108852158724106128684815125 5102444940192474782100709)
                    ·
                      refine ⟨956708426286089021643883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5102444940192474782100709 956708426286089021643883)
                      ·
                        rfl

theorem cell23_1863183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 6, 4].length) (baseStart_1863183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1863183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1863183 prefixEnd_1863183 := by exact prefixLift 1863183
  have htrace : WordTrace (prefixWord ++ tailWord_1863183) baseStart_1863183 baseEnd_1863183 := by
    simpa [prefixWord, tailWord_1863183, baseEnd_1863183] using wordTrace_append hprefix tailTrace_1863183
  have hstable : (prefixWord ++ tailWord_1863183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863183).length < 2 ^ (prefixWord ++ tailWord_1863183).sum := by decide
  have hdescent : baseEnd_1863183 < baseStart_1863183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863214 : List Nat := [4, 1, 3, 1, 2, 1, 2, 3, 2, 4]
def baseStart_1863214 : Nat := 118140960795 + 1863214 * 2 ^ 59
def prefixEnd_1863214 : Nat := 4983230072969 + 3 ^ 40 * 1863214 * 2
def baseEnd_1863214 : Nat := 318908114728792800118747

theorem tailTrace_1863214 : CollatzResearch.WordTrace tailWord_1863214 prefixEnd_1863214 318908114728792800118747 := by
  unfold tailWord_1863214
  simp only [CollatzResearch.WordTrace]
  refine ⟨8494624683987670557773587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45304664981267576308125797 8494624683987670557773587)
  ·
    refine ⟨12741937025981505836660381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8494624683987670557773587 12741937025981505836660381)
    ·
      refine ⟨4778226384743064688747643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12741937025981505836660381 4778226384743064688747643)
      ·
        refine ⟨7167339577114597033121465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4778226384743064688747643 7167339577114597033121465)
        ·
          refine ⟨5375504682835947774841099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7167339577114597033121465 5375504682835947774841099)
          ·
            refine ⟨8063257024253921662261649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5375504682835947774841099 8063257024253921662261649)
            ·
              refine ⟨6047442768190441246696237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8063257024253921662261649 6047442768190441246696237)
              ·
                refine ⟨2267791038071415467511089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6047442768190441246696237 2267791038071415467511089)
                ·
                  refine ⟨1700843278553561600633317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2267791038071415467511089 1700843278553561600633317)
                  ·
                    refine ⟨318908114728792800118747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1700843278553561600633317 318908114728792800118747)
                    ·
                      rfl

theorem cell23_1863214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_1863214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1863214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1863214 prefixEnd_1863214 := by exact prefixLift 1863214
  have htrace : WordTrace (prefixWord ++ tailWord_1863214) baseStart_1863214 baseEnd_1863214 := by
    simpa [prefixWord, tailWord_1863214, baseEnd_1863214] using wordTrace_append hprefix tailTrace_1863214
  have hstable : (prefixWord ++ tailWord_1863214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863214).length < 2 ^ (prefixWord ++ tailWord_1863214).sum := by decide
  have hdescent : baseEnd_1863214 < baseStart_1863214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863237 : List Nat := [1, 3, 1, 1, 1, 4, 2, 2, 4, 1, 3]
def baseStart_1863237 : Nat := 118140960795 + 1863237 * 2 ^ 59
def prefixEnd_1863237 : Nat := 4983230072969 + 3 ^ 40 * 1863237 * 2
def baseEnd_1863237 : Nat := 956736154241431810368635

theorem tailTrace_1863237 : CollatzResearch.WordTrace tailWord_1863237 prefixEnd_1863237 956736154241431810368635 := by
  unfold tailWord_1863237
  simp only [CollatzResearch.WordTrace]
  refine ⟨67957836350818039390275965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45305224233878692926850643 67957836350818039390275965)
  ·
    refine ⟨25484188631556764771353487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67957836350818039390275965 25484188631556764771353487)
    ·
      refine ⟨38226282947335147157030231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25484188631556764771353487 38226282947335147157030231)
      ·
        refine ⟨57339424421002720735545347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38226282947335147157030231 57339424421002720735545347)
        ·
          refine ⟨86009136631504081103318021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57339424421002720735545347 86009136631504081103318021)
          ·
            refine ⟨16126713118407015206872129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86009136631504081103318021 16126713118407015206872129)
            ·
              refine ⟨12095034838805261405154097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16126713118407015206872129 12095034838805261405154097)
              ·
                refine ⟨9071276129103946053865573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12095034838805261405154097 9071276129103946053865573)
                ·
                  refine ⟨1700864274206989885099795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9071276129103946053865573 1700864274206989885099795)
                  ·
                    refine ⟨2551296411310484827649693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1700864274206989885099795 2551296411310484827649693)
                    ·
                      refine ⟨956736154241431810368635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2551296411310484827649693 956736154241431810368635)
                      ·
                        rfl

theorem cell23_1863237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 4, 1, 3].length) (baseStart_1863237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1863237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1863237 prefixEnd_1863237 := by exact prefixLift 1863237
  have htrace : WordTrace (prefixWord ++ tailWord_1863237) baseStart_1863237 baseEnd_1863237 := by
    simpa [prefixWord, tailWord_1863237, baseEnd_1863237] using wordTrace_append hprefix tailTrace_1863237
  have hstable : (prefixWord ++ tailWord_1863237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863237).length < 2 ^ (prefixWord ++ tailWord_1863237).sum := by decide
  have hdescent : baseEnd_1863237 < baseStart_1863237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863290 : List Nat := [3, 1, 1, 1, 1, 1, 1, 4, 4, 2, 4]
def baseStart_1863290 : Nat := 118140960795 + 1863290 * 2 ^ 59
def prefixEnd_1863290 : Nat := 4983230072969 + 3 ^ 40 * 1863290 * 2
def baseEnd_1863290 : Nat := 956763368716120103005891

theorem tailTrace_1863290 : CollatzResearch.WordTrace tailWord_1863290 prefixEnd_1863290 956763368716120103005891 := by
  unfold tailWord_1863290
  simp only [CollatzResearch.WordTrace]
  refine ⟨16989942354906507360488831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45306512946417352961303549 16989942354906507360488831)
  ·
    refine ⟨25484913532359761040733247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16989942354906507360488831 25484913532359761040733247)
    ·
      refine ⟨38227370298539641561099871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25484913532359761040733247 38227370298539641561099871)
      ·
        refine ⟨57341055447809462341649807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38227370298539641561099871 57341055447809462341649807)
        ·
          refine ⟨86011583171714193512474711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57341055447809462341649807 86011583171714193512474711)
          ·
            refine ⟨129017374757571290268712067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86011583171714193512474711 129017374757571290268712067)
            ·
              refine ⟨193526062136356935403068101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129017374757571290268712067 193526062136356935403068101)
              ·
                refine ⟨36286136650566925388075269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 193526062136356935403068101 36286136650566925388075269)
                ·
                  refine ⟨6803650621981298510264113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36286136650566925388075269 6803650621981298510264113)
                  ·
                    refine ⟨5102737966485973882698085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6803650621981298510264113 5102737966485973882698085)
                    ·
                      refine ⟨956763368716120103005891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5102737966485973882698085 956763368716120103005891)
                      ·
                        rfl

theorem cell23_1863290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 4, 2, 4].length) (baseStart_1863290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1863290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1863290 prefixEnd_1863290 := by exact prefixLift 1863290
  have htrace : WordTrace (prefixWord ++ tailWord_1863290) baseStart_1863290 baseEnd_1863290 := by
    simpa [prefixWord, tailWord_1863290, baseEnd_1863290] using wordTrace_append hprefix tailTrace_1863290
  have hstable : (prefixWord ++ tailWord_1863290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863290).length < 2 ^ (prefixWord ++ tailWord_1863290).sum := by decide
  have hdescent : baseEnd_1863290 < baseStart_1863290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863297 : List Nat := [1, 2, 4, 2, 1, 3, 1, 1, 2, 1, 5]
def baseStart_1863297 : Nat := 118140960795 + 1863297 * 2 ^ 59
def prefixEnd_1863297 : Nat := 4983230072969 + 3 ^ 40 * 1863297 * 2
def baseEnd_1863297 : Nat := 956766963080701575618359

theorem tailTrace_1863297 : CollatzResearch.WordTrace tailWord_1863297 prefixEnd_1863297 956766963080701575618359 := by
  unfold tailWord_1863297
  simp only [CollatzResearch.WordTrace]
  refine ⟨67960024730600669637460145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45306683153733779758306763 67960024730600669637460145)
  ·
    refine ⟨50970018547950502228095109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67960024730600669637460145 50970018547950502228095109)
    ·
      refine ⟨9556878477740719167767833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50970018547950502228095109 9556878477740719167767833)
      ·
        refine ⟨7167658858305539375825875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9556878477740719167767833 7167658858305539375825875)
        ·
          refine ⟨10751488287458309063738813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7167658858305539375825875 10751488287458309063738813)
          ·
            refine ⟨4031808107796865898902055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10751488287458309063738813 4031808107796865898902055)
            ·
              refine ⟨6047712161695298848353083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4031808107796865898902055 6047712161695298848353083)
              ·
                refine ⟨9071568242542948272529625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6047712161695298848353083 9071568242542948272529625)
                ·
                  refine ⟨6803676181907211204397219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9071568242542948272529625 6803676181907211204397219)
                  ·
                    refine ⟨10205514272860816806595829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6803676181907211204397219 10205514272860816806595829)
                    ·
                      refine ⟨956766963080701575618359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10205514272860816806595829 956766963080701575618359)
                      ·
                        rfl

theorem cell23_1863297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_1863297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1863297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1863297 prefixEnd_1863297 := by exact prefixLift 1863297
  have htrace : WordTrace (prefixWord ++ tailWord_1863297) baseStart_1863297 baseEnd_1863297 := by
    simpa [prefixWord, tailWord_1863297, baseEnd_1863297] using wordTrace_append hprefix tailTrace_1863297
  have hstable : (prefixWord ++ tailWord_1863297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863297).length < 2 ^ (prefixWord ++ tailWord_1863297).sum := by decide
  have hdescent : baseEnd_1863297 < baseStart_1863297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863317 : List Nat := [1, 3, 2, 1, 1, 1, 1, 8, 5]
def baseStart_1863317 : Nat := 118140960795 + 1863317 * 2 ^ 59
def prefixEnd_1863317 : Nat := 4983230072969 + 3 ^ 40 * 1863317 * 2
def baseEnd_1863317 : Nat := 106308581410421277485363

theorem tailTrace_1863317 : CollatzResearch.WordTrace tailWord_1863317 prefixEnd_1863317 106308581410421277485363 := by
  unfold tailWord_1863317
  simp only [CollatzResearch.WordTrace]
  refine ⟨67960754190528213053188205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45307169460352142035458803 67960754190528213053188205)
  ·
    refine ⟨25485282821448079894945577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67960754190528213053188205 25485282821448079894945577)
    ·
      refine ⟨19113962116086059921209183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25485282821448079894945577 19113962116086059921209183)
      ·
        refine ⟨28670943174129089881813775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19113962116086059921209183 28670943174129089881813775)
        ·
          refine ⟨43006414761193634822720663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28670943174129089881813775 43006414761193634822720663)
          ·
            refine ⟨64509622141790452234080995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43006414761193634822720663 64509622141790452234080995)
            ·
              refine ⟨96764433212685678351121493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64509622141790452234080995 96764433212685678351121493)
              ·
                refine ⟨1133958201711160293177205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 96764433212685678351121493 1133958201711160293177205)
                ·
                  refine ⟨106308581410421277485363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1133958201711160293177205 106308581410421277485363)
                  ·
                    rfl

theorem cell23_1863317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 8, 5].length) (baseStart_1863317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1863317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1863317 prefixEnd_1863317 := by exact prefixLift 1863317
  have htrace : WordTrace (prefixWord ++ tailWord_1863317) baseStart_1863317 baseEnd_1863317 := by
    simpa [prefixWord, tailWord_1863317, baseEnd_1863317] using wordTrace_append hprefix tailTrace_1863317
  have hstable : (prefixWord ++ tailWord_1863317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863317).length < 2 ^ (prefixWord ++ tailWord_1863317).sum := by decide
  have hdescent : baseEnd_1863317 < baseStart_1863317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863328 : List Nat := [2, 1, 1, 4, 3, 1, 4, 1, 2, 2, 2]
def baseStart_1863328 : Nat := 118140960795 + 1863328 * 2 ^ 59
def prefixEnd_1863328 : Nat := 4983230072969 + 3 ^ 40 * 1863328 * 2
def baseEnd_1863328 : Nat := 956782880980990954330717

theorem tailTrace_1863328 : CollatzResearch.WordTrace tailWord_1863328 prefixEnd_1863328 956782880980990954330717 := by
  unfold tailWord_1863328
  simp only [CollatzResearch.WordTrace]
  refine ⟨33980577696744180965919319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45307436928992241287892425 33980577696744180965919319)
  ·
    refine ⟨50970866545116271448878979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33980577696744180965919319 50970866545116271448878979)
    ·
      refine ⟨76456299817674407173318469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50970866545116271448878979 76456299817674407173318469)
      ·
        refine ⟨14335556215813951344997213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76456299817674407173318469 14335556215813951344997213)
        ·
          refine ⟨5375833580930231754373955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14335556215813951344997213 5375833580930231754373955)
          ·
            refine ⟨8063750371395347631560933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5375833580930231754373955 8063750371395347631560933)
            ·
              refine ⟨1511953194636627680917675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8063750371395347631560933 1511953194636627680917675)
              ·
                refine ⟨2267929791954941521376513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1511953194636627680917675 2267929791954941521376513)
                ·
                  refine ⟨1700947343966206141032385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2267929791954941521376513 1700947343966206141032385)
                  ·
                    refine ⟨1275710507974654605774289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1700947343966206141032385 1275710507974654605774289)
                    ·
                      refine ⟨956782880980990954330717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1275710507974654605774289 956782880980990954330717)
                      ·
                        rfl

theorem cell23_1863328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4, 1, 2, 2, 2].length) (baseStart_1863328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1863328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1863328 prefixEnd_1863328 := by exact prefixLift 1863328
  have htrace : WordTrace (prefixWord ++ tailWord_1863328) baseStart_1863328 baseEnd_1863328 := by
    simpa [prefixWord, tailWord_1863328, baseEnd_1863328] using wordTrace_append hprefix tailTrace_1863328
  have hstable : (prefixWord ++ tailWord_1863328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863328).length < 2 ^ (prefixWord ++ tailWord_1863328).sum := by decide
  have hdescent : baseEnd_1863328 < baseStart_1863328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863347 : List Nat := [1, 1, 1, 2, 3, 3, 4, 1, 2, 5]
def baseStart_1863347 : Nat := 118140960795 + 1863347 * 2 ^ 59
def prefixEnd_1863347 : Nat := 4983230072969 + 3 ^ 40 * 1863347 * 2
def baseEnd_1863347 : Nat := 318930879037808793331043

theorem tailTrace_1863347 : CollatzResearch.WordTrace tailWord_1863347 prefixEnd_1863347 318930879037808793331043 := by
  unfold tailWord_1863347
  simp only [CollatzResearch.WordTrace]
  refine ⟨67961848380419528176780295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45307898920279685451186863 67961848380419528176780295)
  ·
    refine ⟨101942772570629292265170443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67961848380419528176780295 101942772570629292265170443)
    ·
      refine ⟨152914158855943938397755665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101942772570629292265170443 152914158855943938397755665)
      ·
        refine ⟨114685619141957953798316749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152914158855943938397755665 114685619141957953798316749)
        ·
          refine ⟨43007107178234232674368781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114685619141957953798316749 43007107178234232674368781)
          ·
            refine ⟨16127665191837837252888293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43007107178234232674368781 16127665191837837252888293)
            ·
              refine ⟨3023937223469594484916555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16127665191837837252888293 3023937223469594484916555)
              ·
                refine ⟨4535905835204391727374833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3023937223469594484916555 4535905835204391727374833)
                ·
                  refine ⟨3401929376403293795531125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4535905835204391727374833 3401929376403293795531125)
                  ·
                    refine ⟨318930879037808793331043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3401929376403293795531125 318930879037808793331043)
                    ·
                      rfl

theorem cell23_1863347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 1, 2, 5].length) (baseStart_1863347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1863347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1863347 prefixEnd_1863347 := by exact prefixLift 1863347
  have htrace : WordTrace (prefixWord ++ tailWord_1863347) baseStart_1863347 baseEnd_1863347 := by
    simpa [prefixWord, tailWord_1863347, baseEnd_1863347] using wordTrace_append hprefix tailTrace_1863347
  have hstable : (prefixWord ++ tailWord_1863347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863347).length < 2 ^ (prefixWord ++ tailWord_1863347).sum := by decide
  have hdescent : baseEnd_1863347 < baseStart_1863347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863367 : List Nat := [1, 1, 4, 1, 1, 1, 3, 4, 2, 1, 4]
def baseStart_1863367 : Nat := 118140960795 + 1863367 * 2 ^ 59
def prefixEnd_1863367 : Nat := 4983230072969 + 3 ^ 40 * 1863367 * 2
def baseEnd_1863367 : Nat := 956802906726516301743037

theorem tailTrace_1863367 : CollatzResearch.WordTrace tailWord_1863367 prefixEnd_1863367 956802906726516301743037 := by
  unfold tailWord_1863367
  simp only [CollatzResearch.WordTrace]
  refine ⟨67962577840347071592508355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45308385226898047728338903 67962577840347071592508355)
  ·
    refine ⟨101943866760520607388762533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67962577840347071592508355 101943866760520607388762533)
    ·
      refine ⟨19114475017597613885392975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101943866760520607388762533 19114475017597613885392975)
      ·
        refine ⟨28671712526396420828089463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19114475017597613885392975 28671712526396420828089463)
        ·
          refine ⟨43007568789594631242134195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28671712526396420828089463 43007568789594631242134195)
          ·
            refine ⟨64511353184391946863201293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43007568789594631242134195 64511353184391946863201293)
            ·
              refine ⟨24191757444146980073700485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64511353184391946863201293 24191757444146980073700485)
              ·
                refine ⟨4535954520777558763818841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24191757444146980073700485 4535954520777558763818841)
                ·
                  refine ⟨3401965890583169072864131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4535954520777558763818841 3401965890583169072864131)
                  ·
                    refine ⟨5102948835874753609296197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3401965890583169072864131 5102948835874753609296197)
                    ·
                      refine ⟨956802906726516301743037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5102948835874753609296197 956802906726516301743037)
                      ·
                        rfl

theorem cell23_1863367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4, 2, 1, 4].length) (baseStart_1863367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1863367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1863367 prefixEnd_1863367 := by exact prefixLift 1863367
  have htrace : WordTrace (prefixWord ++ tailWord_1863367) baseStart_1863367 baseEnd_1863367 := by
    simpa [prefixWord, tailWord_1863367, baseEnd_1863367] using wordTrace_append hprefix tailTrace_1863367
  have hstable : (prefixWord ++ tailWord_1863367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863367).length < 2 ^ (prefixWord ++ tailWord_1863367).sum := by decide
  have hdescent : baseEnd_1863367 < baseStart_1863367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863384 : List Nat := [2, 1, 2, 2, 3, 1, 3, 1, 2, 4, 2]
def baseStart_1863384 : Nat := 118140960795 + 1863384 * 2 ^ 59
def prefixEnd_1863384 : Nat := 4983230072969 + 3 ^ 40 * 1863384 * 2
def baseEnd_1863384 : Nat := 956811635897642735230459

theorem tailTrace_1863384 : CollatzResearch.WordTrace tailWord_1863384 prefixEnd_1863384 956811635897642735230459 := by
  unfold tailWord_1863384
  simp only [CollatzResearch.WordTrace]
  refine ⟨33981598940642741747938603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45308798587523655663918137 33981598940642741747938603)
  ·
    refine ⟨50972398410964112621907905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33981598940642741747938603 50972398410964112621907905)
    ·
      refine ⟨38229298808223084466430929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50972398410964112621907905 38229298808223084466430929)
      ·
        refine ⟨28671974106167313349823197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38229298808223084466430929 28671974106167313349823197)
        ·
          refine ⟨10751990289812742506183699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28671974106167313349823197 10751990289812742506183699)
          ·
            refine ⟨16127985434719113759275549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10751990289812742506183699 16127985434719113759275549)
            ·
              refine ⟨6047994538019667659728331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16127985434719113759275549 6047994538019667659728331)
              ·
                refine ⟨9071991807029501489592497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6047994538019667659728331 9071991807029501489592497)
                ·
                  refine ⟨6803993855272126117194373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9071991807029501489592497 6803993855272126117194373)
                  ·
                    refine ⟨1275748847863523646973945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6803993855272126117194373 1275748847863523646973945)
                    ·
                      refine ⟨956811635897642735230459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1275748847863523646973945 956811635897642735230459)
                      ·
                        rfl

theorem cell23_1863384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 2, 4, 2].length) (baseStart_1863384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1863384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1863384 prefixEnd_1863384 := by exact prefixLift 1863384
  have htrace : WordTrace (prefixWord ++ tailWord_1863384) baseStart_1863384 baseEnd_1863384 := by
    simpa [prefixWord, tailWord_1863384, baseEnd_1863384] using wordTrace_append hprefix tailTrace_1863384
  have hstable : (prefixWord ++ tailWord_1863384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863384).length < 2 ^ (prefixWord ++ tailWord_1863384).sum := by decide
  have hdescent : baseEnd_1863384 < baseStart_1863384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863404 : List Nat := [2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 3]
def baseStart_1863404 : Nat := 118140960795 + 1863404 * 2 ^ 59
def prefixEnd_1863404 : Nat := 4983230072969 + 3 ^ 40 * 1863404 * 2
def baseEnd_1863404 : Nat := 956821905510732656980367

theorem tailTrace_1863404 : CollatzResearch.WordTrace tailWord_1863404 prefixEnd_1863404 956821905510732656980367 := by
  unfold tailWord_1863404
  simp only [CollatzResearch.WordTrace]
  refine ⟨33981963670606513455802633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45309284894142017941070177 33981963670606513455802633)
  ·
    refine ⟨25486472752954885091851975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33981963670606513455802633 25486472752954885091851975)
    ·
      refine ⟨38229709129432327637777963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25486472752954885091851975 38229709129432327637777963)
      ·
        refine ⟨57344563694148491456666945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38229709129432327637777963 57344563694148491456666945)
        ·
          refine ⟨43008422770611368592500209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57344563694148491456666945 43008422770611368592500209)
          ·
            refine ⟨32256317077958526444375157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43008422770611368592500209 32256317077958526444375157)
            ·
              refine ⟨3024029726058611854160171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32256317077958526444375157 3024029726058611854160171)
              ·
                refine ⟨4536044589087917781240257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3024029726058611854160171 4536044589087917781240257)
                ·
                  refine ⟨3402033441815938335930193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4536044589087917781240257 3402033441815938335930193)
                  ·
                    refine ⟨2551525081361953751947645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3402033441815938335930193 2551525081361953751947645)
                    ·
                      refine ⟨956821905510732656980367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2551525081361953751947645 956821905510732656980367)
                      ·
                        rfl

theorem cell23_1863404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 3].length) (baseStart_1863404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1863404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1863404 prefixEnd_1863404 := by exact prefixLift 1863404
  have htrace : WordTrace (prefixWord ++ tailWord_1863404) baseStart_1863404 baseEnd_1863404 := by
    simpa [prefixWord, tailWord_1863404, baseEnd_1863404] using wordTrace_append hprefix tailTrace_1863404
  have hstable : (prefixWord ++ tailWord_1863404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863404).length < 2 ^ (prefixWord ++ tailWord_1863404).sum := by decide
  have hdescent : baseEnd_1863404 < baseStart_1863404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863468 : List Nat := [2, 2, 1, 1, 1, 5, 3, 3, 1, 1, 3]
def baseStart_1863468 : Nat := 118140960795 + 1863468 * 2 ^ 59
def prefixEnd_1863468 : Nat := 4983230072969 + 3 ^ 40 * 1863468 * 2
def baseEnd_1863468 : Nat := 956854768272620406580073

theorem tailTrace_1863468 : CollatzResearch.WordTrace tailWord_1863468 prefixEnd_1863468 956854768272620406580073 := by
  unfold tailWord_1863468
  simp only [CollatzResearch.WordTrace]
  refine ⟨33983130806490582920967529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45310841075320777227956705 33983130806490582920967529)
  ·
    refine ⟨25487348104867937190725647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33983130806490582920967529 25487348104867937190725647)
    ·
      refine ⟨38231022157301905786088471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25487348104867937190725647 38231022157301905786088471)
      ·
        refine ⟨57346533235952858679132707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38231022157301905786088471 57346533235952858679132707)
        ·
          refine ⟨86019799853929288018699061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57346533235952858679132707 86019799853929288018699061)
          ·
            refine ⟨8064356236305870751753037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86019799853929288018699061 8064356236305870751753037)
            ·
              refine ⟨3024133588614701531907389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8064356236305870751753037 3024133588614701531907389)
              ·
                refine ⟨1134050095730513074465271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3024133588614701531907389 1134050095730513074465271)
                ·
                  refine ⟨1701075143595769611697907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1134050095730513074465271 1701075143595769611697907)
                  ·
                    refine ⟨2551612715393654417546861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1701075143595769611697907 2551612715393654417546861)
                    ·
                      refine ⟨956854768272620406580073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2551612715393654417546861 956854768272620406580073)
                      ·
                        rfl

theorem cell23_1863468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 3, 1, 1, 3].length) (baseStart_1863468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1863468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1863468 prefixEnd_1863468 := by exact prefixLift 1863468
  have htrace : WordTrace (prefixWord ++ tailWord_1863468) baseStart_1863468 baseEnd_1863468 := by
    simpa [prefixWord, tailWord_1863468, baseEnd_1863468] using wordTrace_append hprefix tailTrace_1863468
  have hstable : (prefixWord ++ tailWord_1863468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863468).length < 2 ^ (prefixWord ++ tailWord_1863468).sum := by decide
  have hdescent : baseEnd_1863468 < baseStart_1863468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863478 : List Nat := [5, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2]
def baseStart_1863478 : Nat := 118140960795 + 1863478 * 2 ^ 59
def prefixEnd_1863478 : Nat := 4983230072969 + 3 ^ 40 * 1863478 * 2
def baseEnd_1863478 : Nat := 956859903079165367455027

theorem tailTrace_1863478 : CollatzResearch.WordTrace tailWord_1863478 prefixEnd_1863478 956859903079165367455027 := by
  unfold tailWord_1863478
  simp only [CollatzResearch.WordTrace]
  refine ⟨4247914146434058596862443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45311084228629958366532725 4247914146434058596862443)
  ·
    refine ⟨6371871219651087895293665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4247914146434058596862443 6371871219651087895293665)
    ·
      refine ⟨4778903414738315921470249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6371871219651087895293665 4778903414738315921470249)
      ·
        refine ⟨3584177561053736941102687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4778903414738315921470249 3584177561053736941102687)
        ·
          refine ⟨5376266341580605411654031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3584177561053736941102687 5376266341580605411654031)
          ·
            refine ⟨8064399512370908117481047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5376266341580605411654031 8064399512370908117481047)
            ·
              refine ⟨12096599268556362176221571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8064399512370908117481047 12096599268556362176221571)
              ·
                refine ⟨18144898902834543264332357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12096599268556362176221571 18144898902834543264332357)
                ·
                  refine ⟨3402168544281476862062317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18144898902834543264332357 3402168544281476862062317)
                  ·
                    refine ⟨1275813204105553823273369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3402168544281476862062317 1275813204105553823273369)
                    ·
                      refine ⟨956859903079165367455027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1275813204105553823273369 956859903079165367455027)
                      ·
                        rfl

theorem cell23_1863478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_1863478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1863478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1863478 prefixEnd_1863478 := by exact prefixLift 1863478
  have htrace : WordTrace (prefixWord ++ tailWord_1863478) baseStart_1863478 baseEnd_1863478 := by
    simpa [prefixWord, tailWord_1863478, baseEnd_1863478] using wordTrace_append hprefix tailTrace_1863478
  have hstable : (prefixWord ++ tailWord_1863478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863478).length < 2 ^ (prefixWord ++ tailWord_1863478).sum := by decide
  have hdescent : baseEnd_1863478 < baseStart_1863478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863484 : List Nat := [2, 2, 2, 2, 1, 1, 4, 1, 4, 4]
def baseStart_1863484 : Nat := 118140960795 + 1863484 * 2 ^ 59
def prefixEnd_1863484 : Nat := 4983230072969 + 3 ^ 40 * 1863484 * 2
def baseEnd_1863484 : Nat := 318954327987697447993333

theorem tailTrace_1863484 : CollatzResearch.WordTrace tailWord_1863484 prefixEnd_1863484 318954327987697447993333 := by
  unfold tailWord_1863484
  simp only [CollatzResearch.WordTrace]
  refine ⟨33983422590461600287258753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45311230120615467049678337 33983422590461600287258753)
  ·
    refine ⟨25487566942846200215444065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33983422590461600287258753 25487566942846200215444065)
    ·
      refine ⟨19115675207134650161583049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25487566942846200215444065 19115675207134650161583049)
      ·
        refine ⟨14336756405350987621187287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19115675207134650161583049 14336756405350987621187287)
        ·
          refine ⟨21505134608026481431780931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14336756405350987621187287 21505134608026481431780931)
          ·
            refine ⟨32257701912039722147671397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21505134608026481431780931 32257701912039722147671397)
            ·
              refine ⟨6048319108507447902688387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32257701912039722147671397 6048319108507447902688387)
              ·
                refine ⟨9072478662761171854032581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6048319108507447902688387 9072478662761171854032581)
                ·
                  refine ⟨1701089749267719722631109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9072478662761171854032581 1701089749267719722631109)
                  ·
                    refine ⟨318954327987697447993333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1701089749267719722631109 318954327987697447993333)
                    ·
                      rfl

theorem cell23_1863484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 4, 4].length) (baseStart_1863484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1863484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1863484 prefixEnd_1863484 := by exact prefixLift 1863484
  have htrace : WordTrace (prefixWord ++ tailWord_1863484) baseStart_1863484 baseEnd_1863484 := by
    simpa [prefixWord, tailWord_1863484, baseEnd_1863484] using wordTrace_append hprefix tailTrace_1863484
  have hstable : (prefixWord ++ tailWord_1863484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863484).length < 2 ^ (prefixWord ++ tailWord_1863484).sum := by decide
  have hdescent : baseEnd_1863484 < baseStart_1863484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863497 : List Nat := [1, 2, 1, 1, 2, 4, 4, 8]
def baseStart_1863497 : Nat := 118140960795 + 1863497 * 2 ^ 59
def prefixEnd_1863497 : Nat := 4983230072969 + 3 ^ 40 * 1863497 * 2
def baseEnd_1863497 : Nat := 35439617007837066411757

theorem tailTrace_1863497 : CollatzResearch.WordTrace tailWord_1863497 prefixEnd_1863497 35439617007837066411757 := by
  unfold tailWord_1863497
  simp only [CollatzResearch.WordTrace]
  refine ⟨67967319329876103794740745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45311546219917402529827163 67967319329876103794740745)
  ·
    refine ⟨50975489497407077846055559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67967319329876103794740745 50975489497407077846055559)
    ·
      refine ⟨76463234246110616769083339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50975489497407077846055559 76463234246110616769083339)
      ·
        refine ⟨114694851369165925153625009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76463234246110616769083339 114694851369165925153625009)
        ·
          refine ⟨86021138526874443865218757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114694851369165925153625009 86021138526874443865218757)
          ·
            refine ⟨16128963473788958224728517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86021138526874443865218757 16128963473788958224728517)
            ·
              refine ⟨3024180651335429667136597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16128963473788958224728517 3024180651335429667136597)
              ·
                refine ⟨35439617007837066411757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3024180651335429667136597 35439617007837066411757)
                ·
                  rfl

theorem cell23_1863497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 8].length) (baseStart_1863497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1863497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1863497 prefixEnd_1863497 := by exact prefixLift 1863497
  have htrace : WordTrace (prefixWord ++ tailWord_1863497) baseStart_1863497 baseEnd_1863497 := by
    simpa [prefixWord, tailWord_1863497, baseEnd_1863497] using wordTrace_append hprefix tailTrace_1863497
  have hstable : (prefixWord ++ tailWord_1863497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863497).length < 2 ^ (prefixWord ++ tailWord_1863497).sum := by decide
  have hdescent : baseEnd_1863497 < baseStart_1863497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863508 : List Nat := [2, 4, 1, 1, 3, 3, 1, 2, 1, 1, 4]
def baseStart_1863508 : Nat := 118140960795 + 1863508 * 2 ^ 59
def prefixEnd_1863508 : Nat := 4983230072969 + 3 ^ 40 * 1863508 * 2
def baseEnd_1863508 : Nat := 956875307498800250079889

theorem tailTrace_1863508 : CollatzResearch.WordTrace tailWord_1863508 prefixEnd_1863508 956875307498800250079889 := by
  unfold tailWord_1863508
  simp only [CollatzResearch.WordTrace]
  refine ⟨33983860266418126336695589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45311813688557501782260785 33983860266418126336695589)
  ·
    refine ⟨6371973799953398688130423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33983860266418126336695589 6371973799953398688130423)
    ·
      refine ⟨9557960699930098032195635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6371973799953398688130423 9557960699930098032195635)
      ·
        refine ⟨14336941049895147048293453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9557960699930098032195635 14336941049895147048293453)
        ·
          refine ⟨5376352893710680143110045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14336941049895147048293453 5376352893710680143110045)
          ·
            refine ⟨2016132335141505053666267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5376352893710680143110045 2016132335141505053666267)
            ·
              refine ⟨3024198502712257580499401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2016132335141505053666267 3024198502712257580499401)
              ·
                refine ⟨2268148877034193185374551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3024198502712257580499401 2268148877034193185374551)
                ·
                  refine ⟨3402223315551289778061827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2268148877034193185374551 3402223315551289778061827)
                  ·
                    refine ⟨5103334973326934667092741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3402223315551289778061827 5103334973326934667092741)
                    ·
                      refine ⟨956875307498800250079889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5103334973326934667092741 956875307498800250079889)
                      ·
                        rfl

theorem cell23_1863508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 2, 1, 1, 4].length) (baseStart_1863508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1863508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1863508 prefixEnd_1863508 := by exact prefixLift 1863508
  have htrace : WordTrace (prefixWord ++ tailWord_1863508) baseStart_1863508 baseEnd_1863508 := by
    simpa [prefixWord, tailWord_1863508, baseEnd_1863508] using wordTrace_append hprefix tailTrace_1863508
  have hstable : (prefixWord ++ tailWord_1863508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863508).length < 2 ^ (prefixWord ++ tailWord_1863508).sum := by decide
  have hdescent : baseEnd_1863508 < baseStart_1863508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863511 : List Nat := [1, 1, 3, 2, 5, 1, 1, 1, 3, 2, 3]
def baseStart_1863511 : Nat := 118140960795 + 1863511 * 2 ^ 59
def prefixEnd_1863511 : Nat := 4983230072969 + 3 ^ 40 * 1863511 * 2
def baseEnd_1863511 : Nat := 956876847940763738342375

theorem tailTrace_1863511 : CollatzResearch.WordTrace tailWord_1863511 prefixEnd_1863511 956876847940763738342375 := by
  unfold tailWord_1863511
  simp only [CollatzResearch.WordTrace]
  refine ⟨67967829951825384185750387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45311886634550256123833591 67967829951825384185750387)
  ·
    refine ⟨101951744927738076278625581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67967829951825384185750387 101951744927738076278625581)
    ·
      refine ⟨38231904347901778604484593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101951744927738076278625581 38231904347901778604484593)
      ·
        refine ⟨28673928260926333953363445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38231904347901778604484593 28673928260926333953363445)
        ·
          refine ⟨2688180774461843808127823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28673928260926333953363445 2688180774461843808127823)
          ·
            refine ⟨4032271161692765712191735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2688180774461843808127823 4032271161692765712191735)
            ·
              refine ⟨6048406742539148568287603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4032271161692765712191735 6048406742539148568287603)
              ·
                refine ⟨9072610113808722852431405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6048406742539148568287603 9072610113808722852431405)
                ·
                  refine ⟨3402228792678271069661777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9072610113808722852431405 3402228792678271069661777)
                  ·
                    refine ⟨2551671594508703302246333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3402228792678271069661777 2551671594508703302246333)
                    ·
                      refine ⟨956876847940763738342375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2551671594508703302246333 956876847940763738342375)
                      ·
                        rfl

theorem cell23_1863511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 3, 2, 3].length) (baseStart_1863511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1863511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1863511 prefixEnd_1863511 := by exact prefixLift 1863511
  have htrace : WordTrace (prefixWord ++ tailWord_1863511) baseStart_1863511 baseEnd_1863511 := by
    simpa [prefixWord, tailWord_1863511, baseEnd_1863511] using wordTrace_append hprefix tailTrace_1863511
  have hstable : (prefixWord ++ tailWord_1863511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863511).length < 2 ^ (prefixWord ++ tailWord_1863511).sum := by decide
  have hdescent : baseEnd_1863511 < baseStart_1863511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863528 : List Nat := [2, 1, 4, 2, 1, 1, 5, 1, 1, 2, 3]
def baseStart_1863528 : Nat := 118140960795 + 1863528 * 2 ^ 59
def prefixEnd_1863528 : Nat := 4983230072969 + 3 ^ 40 * 1863528 * 2
def baseEnd_1863528 : Nat := 956885577111890171829797

theorem tailTrace_1863528 : CollatzResearch.WordTrace tailWord_1863528 prefixEnd_1863528 956885577111890171829797 := by
  unfold tailWord_1863528
  simp only [CollatzResearch.WordTrace]
  refine ⟨33984224996381898044559619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45312299995175864059412825 33984224996381898044559619)
  ·
    refine ⟨50976337494572847066839429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33984224996381898044559619 50976337494572847066839429)
    ·
      refine ⟨9558063280232408825032393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50976337494572847066839429 9558063280232408825032393)
      ·
        refine ⟨7168547460174306618774295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9558063280232408825032393 7168547460174306618774295)
        ·
          refine ⟨10752821190261459928161443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7168547460174306618774295 10752821190261459928161443)
          ·
            refine ⟨16129231785392189892242165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10752821190261459928161443 16129231785392189892242165)
            ·
              refine ⟨1512115479880517802397703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16129231785392189892242165 1512115479880517802397703)
              ·
                refine ⟨2268173219820776703596555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1512115479880517802397703 2268173219820776703596555)
                ·
                  refine ⟨3402259829731165055394833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2268173219820776703596555 3402259829731165055394833)
                  ·
                    refine ⟨2551694872298373791546125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3402259829731165055394833 2551694872298373791546125)
                    ·
                      refine ⟨956885577111890171829797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2551694872298373791546125 956885577111890171829797)
                      ·
                        rfl

theorem cell23_1863528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_1863528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1863528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1863528 prefixEnd_1863528 := by exact prefixLift 1863528
  have htrace : WordTrace (prefixWord ++ tailWord_1863528) baseStart_1863528 baseEnd_1863528 := by
    simpa [prefixWord, tailWord_1863528, baseEnd_1863528] using wordTrace_append hprefix tailTrace_1863528
  have hstable : (prefixWord ++ tailWord_1863528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863528).length < 2 ^ (prefixWord ++ tailWord_1863528).sum := by decide
  have hdescent : baseEnd_1863528 < baseStart_1863528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863585 : List Nat := [1, 2, 3, 4, 2, 1, 1, 3, 1, 3, 2]
def baseStart_1863585 : Nat := 118140960795 + 1863585 * 2 ^ 59
def prefixEnd_1863585 : Nat := 4983230072969 + 3 ^ 40 * 1863585 * 2
def baseEnd_1863585 : Nat := 956914845509196448817035

theorem tailTrace_1863585 : CollatzResearch.WordTrace tailWord_1863585 prefixEnd_1863585 956914845509196448817035 := by
  unfold tailWord_1863585
  simp only [CollatzResearch.WordTrace]
  refine ⟨67970528953557294823944209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45313685969038196549296139 67970528953557294823944209)
  ·
    refine ⟨50977896715167971117958157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67970528953557294823944209 50977896715167971117958157)
    ·
      refine ⟨19116711268187989169234309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50977896715167971117958157 19116711268187989169234309)
      ·
        refine ⟨3584383362785247969231433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19116711268187989169234309 3584383362785247969231433)
        ·
          refine ⟨2688287522088935976923575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3584383362785247969231433 2688287522088935976923575)
          ·
            refine ⟨4032431283133403965385363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2688287522088935976923575 4032431283133403965385363)
            ·
              refine ⟨6048646924700105948078045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4032431283133403965385363 6048646924700105948078045)
              ·
                refine ⟨2268242596762539730529267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6048646924700105948078045 2268242596762539730529267)
                ·
                  refine ⟨3402363895143809595793901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2268242596762539730529267 3402363895143809595793901)
                  ·
                    refine ⟨1275886460678928598422713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3402363895143809595793901 1275886460678928598422713)
                    ·
                      refine ⟨956914845509196448817035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1275886460678928598422713 956914845509196448817035)
                      ·
                        rfl

theorem cell23_1863585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_1863585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1863585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1863585 prefixEnd_1863585 := by exact prefixLift 1863585
  have htrace : WordTrace (prefixWord ++ tailWord_1863585) baseStart_1863585 baseEnd_1863585 := by
    simpa [prefixWord, tailWord_1863585, baseEnd_1863585] using wordTrace_append hprefix tailTrace_1863585
  have hstable : (prefixWord ++ tailWord_1863585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863585).length < 2 ^ (prefixWord ++ tailWord_1863585).sum := by decide
  have hdescent : baseEnd_1863585 < baseStart_1863585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863587 : List Nat := [1, 1, 1, 4, 1, 2, 1, 1, 11]
def baseStart_1863587 : Nat := 118140960795 + 1863587 * 2 ^ 59
def prefixEnd_1863587 : Nat := 4983230072969 + 3 ^ 40 * 1863587 * 2
def baseEnd_1863587 : Nat := 106323985830056160110225

theorem tailTrace_1863587 : CollatzResearch.WordTrace tailWord_1863587 prefixEnd_1863587 106323985830056160110225 := by
  unfold tailWord_1863587
  simp only [CollatzResearch.WordTrace]
  refine ⟨67970601899550049165517015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45313734599700032777011343 67970601899550049165517015)
  ·
    refine ⟨101955902849325073748275523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67970601899550049165517015 101955902849325073748275523)
    ·
      refine ⟨152933854273987610622413285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101955902849325073748275523 152933854273987610622413285)
      ·
        refine ⟨28675097676372676991702491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152933854273987610622413285 28675097676372676991702491)
        ·
          refine ⟨43012646514559015487553737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28675097676372676991702491 43012646514559015487553737)
          ·
            refine ⟨32259484885919261615665303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43012646514559015487553737 32259484885919261615665303)
            ·
              refine ⟨48389227328878892423497955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32259484885919261615665303 48389227328878892423497955)
              ·
                refine ⟨72583840993318338635246933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48389227328878892423497955 72583840993318338635246933)
                ·
                  refine ⟨106323985830056160110225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 72583840993318338635246933 106323985830056160110225)
                  ·
                    rfl

theorem cell23_1863587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 11].length) (baseStart_1863587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1863587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1863587 prefixEnd_1863587 := by exact prefixLift 1863587
  have htrace : WordTrace (prefixWord ++ tailWord_1863587) baseStart_1863587 baseEnd_1863587 := by
    simpa [prefixWord, tailWord_1863587, baseEnd_1863587] using wordTrace_append hprefix tailTrace_1863587
  have hstable : (prefixWord ++ tailWord_1863587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863587).length < 2 ^ (prefixWord ++ tailWord_1863587).sum := by decide
  have hdescent : baseEnd_1863587 < baseStart_1863587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863615 : List Nat := [1, 1, 2, 2, 2, 1, 7, 1, 2, 2, 2]
def baseStart_1863615 : Nat := 118140960795 + 1863615 * 2 ^ 59
def prefixEnd_1863615 : Nat := 4983230072969 + 3 ^ 40 * 1863615 * 2
def baseEnd_1863615 : Nat := 956930249928831331441897

theorem tailTrace_1863615 : CollatzResearch.WordTrace tailWord_1863615 prefixEnd_1863615 956930249928831331441897 := by
  unfold tailWord_1863615
  simp only [CollatzResearch.WordTrace]
  refine ⟨67971623143448609947536299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45314415428965739965024199 67971623143448609947536299)
  ·
    refine ⟨101957434715172914921304449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67971623143448609947536299 101957434715172914921304449)
    ·
      refine ⟨76468076036379686190978337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101957434715172914921304449 76468076036379686190978337)
      ·
        refine ⟨57351057027284764643233753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76468076036379686190978337 57351057027284764643233753)
        ·
          refine ⟨43013292770463573482425315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57351057027284764643233753 43013292770463573482425315)
          ·
            refine ⟨64519939155695360223637973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43013292770463573482425315 64519939155695360223637973)
            ·
              refine ⟨1512186073961610005241515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 64519939155695360223637973 1512186073961610005241515)
              ·
                refine ⟨2268279110942415007862273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1512186073961610005241515 2268279110942415007862273)
                ·
                  refine ⟨1701209333206811255896705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2268279110942415007862273 1701209333206811255896705)
                  ·
                    refine ⟨1275906999905108441922529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1701209333206811255896705 1275906999905108441922529)
                    ·
                      refine ⟨956930249928831331441897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1275906999905108441922529 956930249928831331441897)
                      ·
                        rfl

theorem cell23_1863615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7, 1, 2, 2, 2].length) (baseStart_1863615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1863615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1863615 prefixEnd_1863615 := by exact prefixLift 1863615
  have htrace : WordTrace (prefixWord ++ tailWord_1863615) baseStart_1863615 baseEnd_1863615 := by
    simpa [prefixWord, tailWord_1863615, baseEnd_1863615] using wordTrace_append hprefix tailTrace_1863615
  have hstable : (prefixWord ++ tailWord_1863615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863615).length < 2 ^ (prefixWord ++ tailWord_1863615).sum := by decide
  have hdescent : baseEnd_1863615 < baseStart_1863615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863651 : List Nat := [1, 1, 1, 6, 1, 3, 1, 2, 2, 5]
def baseStart_1863651 : Nat := 118140960795 + 1863651 * 2 ^ 59
def prefixEnd_1863651 : Nat := 4983230072969 + 3 ^ 40 * 1863651 * 2
def baseEnd_1863651 : Nat := 318982911744131063530577

theorem tailTrace_1863651 : CollatzResearch.WordTrace tailWord_1863651 prefixEnd_1863651 318982911744131063530577 := by
  unfold tailWord_1863651
  simp only [CollatzResearch.WordTrace]
  refine ⟨67972936171318188095846807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45315290780878792063897871 67972936171318188095846807)
  ·
    refine ⟨101959404256977282143770211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67972936171318188095846807 101959404256977282143770211)
    ·
      refine ⟨152939106385465923215655317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101959404256977282143770211 152939106385465923215655317)
      ·
        refine ⟨7169020611818715150733843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 152939106385465923215655317 7169020611818715150733843)
        ·
          refine ⟨10753530917728072726100765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7169020611818715150733843 10753530917728072726100765)
          ·
            refine ⟨4032574094148027272287787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10753530917728072726100765 4032574094148027272287787)
            ·
              refine ⟨6048861141222040908431681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4032574094148027272287787 6048861141222040908431681)
              ·
                refine ⟨4536645855916530681323761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6048861141222040908431681 4536645855916530681323761)
                ·
                  refine ⟨3402484391937398010992821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4536645855916530681323761 3402484391937398010992821)
                  ·
                    refine ⟨318982911744131063530577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3402484391937398010992821 318982911744131063530577)
                    ·
                      rfl

theorem cell23_1863651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 2, 2, 5].length) (baseStart_1863651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1863651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1863651 prefixEnd_1863651 := by exact prefixLift 1863651
  have htrace : WordTrace (prefixWord ++ tailWord_1863651) baseStart_1863651 baseEnd_1863651 := by
    simpa [prefixWord, tailWord_1863651, baseEnd_1863651] using wordTrace_append hprefix tailTrace_1863651
  have hstable : (prefixWord ++ tailWord_1863651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863651).length < 2 ^ (prefixWord ++ tailWord_1863651).sum := by decide
  have hdescent : baseEnd_1863651 < baseStart_1863651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863655 : List Nat := [1, 1, 5, 2, 3, 1, 3, 2, 5]
def baseStart_1863655 : Nat := 118140960795 + 1863655 * 2 ^ 59
def prefixEnd_1863655 : Nat := 4983230072969 + 3 ^ 40 * 1863655 * 2
def baseEnd_1863655 : Nat := 106327865461667908326857

theorem tailTrace_1863655 : CollatzResearch.WordTrace tailWord_1863655 prefixEnd_1863655 106327865461667908326857 := by
  unfold tailWord_1863655
  simp only [CollatzResearch.WordTrace]
  refine ⟨67973082063303696778992419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45315388042202464519328279 67973082063303696778992419)
  ·
    refine ⟨101959623094955545168488629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67973082063303696778992419 101959623094955545168488629)
    ·
      refine ⟨9558714665152082359545809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101959623094955545168488629 9558714665152082359545809)
      ·
        refine ⟨7169035998864061769659357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9558714665152082359545809 7169035998864061769659357)
        ·
          refine ⟨2688388499574023163622259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7169035998864061769659357 2688388499574023163622259)
          ·
            refine ⟨4032582749361034745433389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2688388499574023163622259 4032582749361034745433389)
            ·
              refine ⟨1512218531010388029537521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4032582749361034745433389 1512218531010388029537521)
              ·
                refine ⟨1134163898257791022153141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1512218531010388029537521 1134163898257791022153141)
                ·
                  refine ⟨106327865461667908326857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1134163898257791022153141 106327865461667908326857)
                  ·
                    rfl

theorem cell23_1863655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3, 2, 5].length) (baseStart_1863655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1863655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1863655 prefixEnd_1863655 := by exact prefixLift 1863655
  have htrace : WordTrace (prefixWord ++ tailWord_1863655) baseStart_1863655 baseEnd_1863655 := by
    simpa [prefixWord, tailWord_1863655, baseEnd_1863655] using wordTrace_append hprefix tailTrace_1863655
  have hstable : (prefixWord ++ tailWord_1863655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863655).length < 2 ^ (prefixWord ++ tailWord_1863655).sum := by decide
  have hdescent : baseEnd_1863655 < baseStart_1863655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863681 : List Nat := [1, 2, 4, 1, 2, 1, 2, 1, 5, 4]
def baseStart_1863681 : Nat := 118140960795 + 1863681 * 2 ^ 59
def prefixEnd_1863681 : Nat := 4983230072969 + 3 ^ 40 * 1863681 * 2
def baseEnd_1863681 : Nat := 318988046550676024405531

theorem tailTrace_1863681 : CollatzResearch.WordTrace tailWord_1863681 prefixEnd_1863681 318988046550676024405531 := by
  unfold tailWord_1863681
  simp only [CollatzResearch.WordTrace]
  refine ⟨67974030361209503219438897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45316020240806335479625931 67974030361209503219438897)
  ·
    refine ⟨50980522770907127414579173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67974030361209503219438897 50980522770907127414579173)
    ·
      refine ⟨9558848019545086390233595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50980522770907127414579173 9558848019545086390233595)
      ·
        refine ⟨14338272029317629585350393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9558848019545086390233595 14338272029317629585350393)
        ·
          refine ⟨10753704021988222189012795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14338272029317629585350393 10753704021988222189012795)
          ·
            refine ⟨16130556032982333283519193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10753704021988222189012795 16130556032982333283519193)
            ·
              refine ⟨12097917024736749962639395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16130556032982333283519193 12097917024736749962639395)
              ·
                refine ⟨18146875537105124943959093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12097917024736749962639395 18146875537105124943959093)
                ·
                  refine ⟨1701269581603605463496165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18146875537105124943959093 1701269581603605463496165)
                  ·
                    refine ⟨318988046550676024405531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1701269581603605463496165 318988046550676024405531)
                    ·
                      rfl

theorem cell23_1863681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_1863681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1863681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1863681 prefixEnd_1863681 := by exact prefixLift 1863681
  have htrace : WordTrace (prefixWord ++ tailWord_1863681) baseStart_1863681 baseEnd_1863681 := by
    simpa [prefixWord, tailWord_1863681, baseEnd_1863681] using wordTrace_append hprefix tailTrace_1863681
  have hstable : (prefixWord ++ tailWord_1863681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863681).length < 2 ^ (prefixWord ++ tailWord_1863681).sum := by decide
  have hdescent : baseEnd_1863681 < baseStart_1863681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863708 : List Nat := [2, 2, 3, 1, 3, 1, 2, 2, 2, 2, 3]
def baseStart_1863708 : Nat := 118140960795 + 1863708 * 2 ^ 59
def prefixEnd_1863708 : Nat := 4983230072969 + 3 ^ 40 * 1863708 * 2
def baseEnd_1863708 : Nat := 956978003629699467578969

theorem tailTrace_1863708 : CollatzResearch.WordTrace tailWord_1863708 prefixEnd_1863708 956978003629699467578969 := by
  unfold tailWord_1863708
  simp only [CollatzResearch.WordTrace]
  refine ⟨33987507566055843415335889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45316676754741124553781185 33987507566055843415335889)
  ·
    refine ⟨25490630674541882561501917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33987507566055843415335889 25490630674541882561501917)
    ·
      refine ⟨9558986502953205960563219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25490630674541882561501917 9558986502953205960563219)
      ·
        refine ⟨14338479754429808940844829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9558986502953205960563219 14338479754429808940844829)
        ·
          refine ⟨5376929907911178352816811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14338479754429808940844829 5376929907911178352816811)
          ·
            refine ⟨8065394861866767529225217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5376929907911178352816811 8065394861866767529225217)
            ·
              refine ⟨6049046146400075646918913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8065394861866767529225217 6049046146400075646918913)
              ·
                refine ⟨4536784609800056735189185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6049046146400075646918913 4536784609800056735189185)
                ·
                  refine ⟨3402588457350042551391889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4536784609800056735189185 3402588457350042551391889)
                  ·
                    refine ⟨2551941343012531913543917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3402588457350042551391889 2551941343012531913543917)
                    ·
                      refine ⟨956978003629699467578969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2551941343012531913543917 956978003629699467578969)
                      ·
                        rfl

theorem cell23_1863708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_1863708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1863708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1863708 prefixEnd_1863708 := by exact prefixLift 1863708
  have htrace : WordTrace (prefixWord ++ tailWord_1863708) baseStart_1863708 baseEnd_1863708 := by
    simpa [prefixWord, tailWord_1863708, baseEnd_1863708] using wordTrace_append hprefix tailTrace_1863708
  have hstable : (prefixWord ++ tailWord_1863708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863708).length < 2 ^ (prefixWord ++ tailWord_1863708).sum := by decide
  have hdescent : baseEnd_1863708 < baseStart_1863708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863711 : List Nat := [1, 1, 2, 4, 1, 2, 4, 2, 6]
def baseStart_1863711 : Nat := 118140960795 + 1863711 * 2 ^ 59
def prefixEnd_1863711 : Nat := 4983230072969 + 3 ^ 40 * 1863711 * 2
def baseEnd_1863711 : Nat := 106331060452406995093495

theorem tailTrace_1863711 : CollatzResearch.WordTrace tailWord_1863711 prefixEnd_1863711 106331060452406995093495 := by
  unfold tailWord_1863711
  simp only [CollatzResearch.WordTrace]
  refine ⟨67975124551100818343030987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45316749700733878895353991 67975124551100818343030987)
  ·
    refine ⟨101962686826651227514546481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67975124551100818343030987 101962686826651227514546481)
    ·
      refine ⟨76472015119988420635909861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101962686826651227514546481 76472015119988420635909861)
      ·
        refine ⟨14338502834997828869233099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76472015119988420635909861 14338502834997828869233099)
        ·
          refine ⟨21507754252496743303849649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14338502834997828869233099 21507754252496743303849649)
          ·
            refine ⟨16130815689372557477887237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21507754252496743303849649 16130815689372557477887237)
            ·
              refine ⟨3024527941757354527103857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16130815689372557477887237 3024527941757354527103857)
              ·
                refine ⟨2268395956318015895327893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3024527941757354527103857 2268395956318015895327893)
                ·
                  refine ⟨106331060452406995093495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2268395956318015895327893 106331060452406995093495)
                  ·
                    rfl

theorem cell23_1863711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 2, 6].length) (baseStart_1863711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1863711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1863711 prefixEnd_1863711 := by exact prefixLift 1863711
  have htrace : WordTrace (prefixWord ++ tailWord_1863711) baseStart_1863711 baseEnd_1863711 := by
    simpa [prefixWord, tailWord_1863711, baseEnd_1863711] using wordTrace_append hprefix tailTrace_1863711
  have hstable : (prefixWord ++ tailWord_1863711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863711).length < 2 ^ (prefixWord ++ tailWord_1863711).sum := by decide
  have hdescent : baseEnd_1863711 < baseStart_1863711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863741 : List Nat := [1, 4, 1, 3, 1, 1, 1, 3, 3, 5]
def baseStart_1863741 : Nat := 118140960795 + 1863741 * 2 ^ 59
def prefixEnd_1863741 : Nat := 4983230072969 + 3 ^ 40 * 1863741 * 2
def baseEnd_1863741 : Nat := 318998316163765946155439

theorem tailTrace_1863741 : CollatzResearch.WordTrace tailWord_1863741 prefixEnd_1863741 318998316163765946155439 := by
  unfold tailWord_1863741
  simp only [CollatzResearch.WordTrace]
  refine ⟨67976218740992133466623077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45317479160661422311082051 67976218740992133466623077)
  ·
    refine ⟨12745541013936025024991827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67976218740992133466623077 12745541013936025024991827)
    ·
      refine ⟨19118311520904037537487741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12745541013936025024991827 19118311520904037537487741)
      ·
        refine ⟨7169366820339014076557903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19118311520904037537487741 7169366820339014076557903)
        ·
          refine ⟨10754050230508521114836855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7169366820339014076557903 10754050230508521114836855)
          ·
            refine ⟨16131075345762781672255283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10754050230508521114836855 16131075345762781672255283)
            ·
              refine ⟨24196613018644172508382925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16131075345762781672255283 24196613018644172508382925)
              ·
                refine ⟨9073729881991564690643597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24196613018644172508382925 9073729881991564690643597)
                ·
                  refine ⟨3402648705746836758991349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9073729881991564690643597 3402648705746836758991349)
                  ·
                    refine ⟨318998316163765946155439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3402648705746836758991349 318998316163765946155439)
                    ·
                      rfl

theorem cell23_1863741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 3, 5].length) (baseStart_1863741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1863741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1863741 prefixEnd_1863741 := by exact prefixLift 1863741
  have htrace : WordTrace (prefixWord ++ tailWord_1863741) baseStart_1863741 baseEnd_1863741 := by
    simpa [prefixWord, tailWord_1863741, baseEnd_1863741] using wordTrace_append hprefix tailTrace_1863741
  have hstable : (prefixWord ++ tailWord_1863741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863741).length < 2 ^ (prefixWord ++ tailWord_1863741).sum := by decide
  have hdescent : baseEnd_1863741 < baseStart_1863741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863742 : List Nat := [4, 2, 1, 3, 2, 2, 1, 1, 2, 2, 3]
def baseStart_1863742 : Nat := 118140960795 + 1863742 * 2 ^ 59
def prefixEnd_1863742 : Nat := 4983230072969 + 3 ^ 40 * 1863742 * 2
def baseEnd_1863742 : Nat := 956995461971952334553813

theorem tailTrace_1863742 : CollatzResearch.WordTrace tailWord_1863742 prefixEnd_1863742 956995461971952334553813 := by
  unfold tailWord_1863742
  simp only [CollatzResearch.WordTrace]
  refine ⟨8497031901748563829676185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45317503475992340424939653 8497031901748563829676185)
  ·
    refine ⟨6372773926311422872257139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8497031901748563829676185 6372773926311422872257139)
    ·
      refine ⟨9559160889467134308385709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6372773926311422872257139 9559160889467134308385709)
      ·
        refine ⟨3584685333550175365644641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9559160889467134308385709 3584685333550175365644641)
        ·
          refine ⟨2688514000162631524233481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3584685333550175365644641 2688514000162631524233481)
          ·
            refine ⟨2016385500121973643175111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2688514000162631524233481 2016385500121973643175111)
            ·
              refine ⟨3024578250182960464762667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2016385500121973643175111 3024578250182960464762667)
              ·
                refine ⟨4536867375274440697144001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3024578250182960464762667 4536867375274440697144001)
                ·
                  refine ⟨3402650531455830522858001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4536867375274440697144001 3402650531455830522858001)
                  ·
                    refine ⟨2551987898591872892143501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3402650531455830522858001 2551987898591872892143501)
                    ·
                      refine ⟨956995461971952334553813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2551987898591872892143501 956995461971952334553813)
                      ·
                        rfl

theorem cell23_1863742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_1863742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1863742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1863742 prefixEnd_1863742 := by exact prefixLift 1863742
  have htrace : WordTrace (prefixWord ++ tailWord_1863742) baseStart_1863742 baseEnd_1863742 := by
    simpa [prefixWord, tailWord_1863742, baseEnd_1863742] using wordTrace_append hprefix tailTrace_1863742
  have hstable : (prefixWord ++ tailWord_1863742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863742).length < 2 ^ (prefixWord ++ tailWord_1863742).sum := by decide
  have hdescent : baseEnd_1863742 < baseStart_1863742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863758 : List Nat := [4, 1, 1, 1, 1, 5, 1, 3, 1, 5]
def baseStart_1863758 : Nat := 118140960795 + 1863758 * 2 ^ 59
def prefixEnd_1863758 : Nat := 4983230072969 + 3 ^ 40 * 1863758 * 2
def baseEnd_1863758 : Nat := 319001225887474757317913

theorem tailTrace_1863758 : CollatzResearch.WordTrace tailWord_1863758 prefixEnd_1863758 319001225887474757317913 := by
  unfold tailWord_1863758
  simp only [CollatzResearch.WordTrace]
  refine ⟨8497104847741318171248991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45317892521287030246661285 8497104847741318171248991)
  ·
    refine ⟨12745657271611977256873487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8497104847741318171248991 12745657271611977256873487)
    ·
      refine ⟨19118485907417965885310231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12745657271611977256873487 19118485907417965885310231)
      ·
        refine ⟨28677728861126948827965347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19118485907417965885310231 28677728861126948827965347)
        ·
          refine ⟨43016593291690423241948021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28677728861126948827965347 43016593291690423241948021)
          ·
            refine ⟨4032805621095977178932627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43016593291690423241948021 4032805621095977178932627)
            ·
              refine ⟨6049208431643965768398941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4032805621095977178932627 6049208431643965768398941)
              ·
                refine ⟨2268453161866487163149603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6049208431643965768398941 2268453161866487163149603)
                ·
                  refine ⟨3402679742799730744724405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2268453161866487163149603 3402679742799730744724405)
                  ·
                    refine ⟨319001225887474757317913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3402679742799730744724405 319001225887474757317913)
                    ·
                      rfl

theorem cell23_1863758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 3, 1, 5].length) (baseStart_1863758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1863758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1863758 prefixEnd_1863758 := by exact prefixLift 1863758
  have htrace : WordTrace (prefixWord ++ tailWord_1863758) baseStart_1863758 baseEnd_1863758 := by
    simpa [prefixWord, tailWord_1863758, baseEnd_1863758] using wordTrace_append hprefix tailTrace_1863758
  have hstable : (prefixWord ++ tailWord_1863758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863758).length < 2 ^ (prefixWord ++ tailWord_1863758).sum := by decide
  have hdescent : baseEnd_1863758 < baseStart_1863758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863772 : List Nat := [2, 2, 4, 1, 1, 2, 2, 4, 1, 1, 3]
def baseStart_1863772 : Nat := 118140960795 + 1863772 * 2 ^ 59
def prefixEnd_1863772 : Nat := 4983230072969 + 3 ^ 40 * 1863772 * 2
def baseEnd_1863772 : Nat := 957010866391587217178675

theorem tailTrace_1863772 : CollatzResearch.WordTrace tailWord_1863772 prefixEnd_1863772 957010866391587217178675 := by
  unfold tailWord_1863772
  simp only [CollatzResearch.WordTrace]
  refine ⟨33988674701939912880500785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45318232935919883840667713 33988674701939912880500785)
  ·
    refine ⟨25491506026454934660375589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33988674701939912880500785 25491506026454934660375589)
    ·
      refine ⟨4779657379960300248820423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25491506026454934660375589 4779657379960300248820423)
      ·
        refine ⟨7169486069940450373230635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4779657379960300248820423 7169486069940450373230635)
        ·
          refine ⟨10754229104910675559845953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7169486069940450373230635 10754229104910675559845953)
          ·
            refine ⟨8065671828683006669884465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10754229104910675559845953 8065671828683006669884465)
            ·
              refine ⟨6049253871512255002413349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8065671828683006669884465 6049253871512255002413349)
              ·
                refine ⟨1134235100908547812952503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6049253871512255002413349 1134235100908547812952503)
                ·
                  refine ⟨1701352651362821719428755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1134235100908547812952503 1701352651362821719428755)
                  ·
                    refine ⟨2552028977044232579143133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1701352651362821719428755 2552028977044232579143133)
                    ·
                      refine ⟨957010866391587217178675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2552028977044232579143133 957010866391587217178675)
                      ·
                        rfl

theorem cell23_1863772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_1863772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1863772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1863772 prefixEnd_1863772 := by exact prefixLift 1863772
  have htrace : WordTrace (prefixWord ++ tailWord_1863772) baseStart_1863772 baseEnd_1863772 := by
    simpa [prefixWord, tailWord_1863772, baseEnd_1863772] using wordTrace_append hprefix tailTrace_1863772
  have hstable : (prefixWord ++ tailWord_1863772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863772).length < 2 ^ (prefixWord ++ tailWord_1863772).sum := by decide
  have hdescent : baseEnd_1863772 < baseStart_1863772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863781 : List Nat := [1, 3, 1, 3, 2, 2, 1, 1, 3, 1, 5]
def baseStart_1863781 : Nat := 118140960795 + 1863781 * 2 ^ 59
def prefixEnd_1863781 : Nat := 4983230072969 + 3 ^ 40 * 1863781 * 2
def baseEnd_1863781 : Nat := 957015487717477681966133

theorem tailTrace_1863781 : CollatzResearch.WordTrace tailWord_1863781 prefixEnd_1863781 957015487717477681966133 := by
  unfold tailWord_1863781
  simp only [CollatzResearch.WordTrace]
  refine ⟨67977677660847220298079197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45318451773898146865386131 67977677660847220298079197)
  ·
    refine ⟨25491629122817707611779699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67977677660847220298079197 25491629122817707611779699)
    ·
      refine ⟨38237443684226561417669549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25491629122817707611779699 38237443684226561417669549)
      ·
        refine ⟨14339041381584960531626081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38237443684226561417669549 14339041381584960531626081)
        ·
          refine ⟨10754281036188720398719561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14339041381584960531626081 10754281036188720398719561)
          ·
            refine ⟨8065710777141540299039671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10754281036188720398719561 8065710777141540299039671)
            ·
              refine ⟨12098566165712310448559507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8065710777141540299039671 12098566165712310448559507)
              ·
                refine ⟨18147849248568465672839261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12098566165712310448559507 18147849248568465672839261)
                ·
                  refine ⟨6805443468213174627314723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18147849248568465672839261 6805443468213174627314723)
                  ·
                    refine ⟨10208165202319761940972085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6805443468213174627314723 10208165202319761940972085)
                    ·
                      refine ⟨957015487717477681966133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10208165202319761940972085 957015487717477681966133)
                      ·
                        rfl

theorem cell23_1863781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_1863781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1863781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1863781 prefixEnd_1863781 := by exact prefixLift 1863781
  have htrace : WordTrace (prefixWord ++ tailWord_1863781) baseStart_1863781 baseEnd_1863781 := by
    simpa [prefixWord, tailWord_1863781, baseEnd_1863781] using wordTrace_append hprefix tailTrace_1863781
  have hstable : (prefixWord ++ tailWord_1863781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863781).length < 2 ^ (prefixWord ++ tailWord_1863781).sum := by decide
  have hdescent : baseEnd_1863781 < baseStart_1863781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863788 : List Nat := [2, 2, 1, 1, 3, 5, 1, 1, 1, 6]
def baseStart_1863788 : Nat := 118140960795 + 1863788 * 2 ^ 59
def prefixEnd_1863788 : Nat := 4983230072969 + 3 ^ 40 * 1863788 * 2
def baseEnd_1863788 : Nat := 319006360694019718192867

theorem tailTrace_1863788 : CollatzResearch.WordTrace tailWord_1863788 prefixEnd_1863788 319006360694019718192867 := by
  unfold tailWord_1863788
  simp only [CollatzResearch.WordTrace]
  refine ⟨33988966485910930246792009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45318621981214573662389345 33988966485910930246792009)
  ·
    refine ⟨25491724864433197685094007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33988966485910930246792009 25491724864433197685094007)
    ·
      refine ⟨38237587296649796527641011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25491724864433197685094007 38237587296649796527641011)
      ·
        refine ⟨57356380944974694791461517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38237587296649796527641011 57356380944974694791461517)
        ·
          refine ⟨21508642854365510546798069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57356380944974694791461517 21508642854365510546798069)
          ·
            refine ⟨2016435267596766613762319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21508642854365510546798069 2016435267596766613762319)
            ·
              refine ⟨3024652901395149920643479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2016435267596766613762319 3024652901395149920643479)
              ·
                refine ⟨4536979352092724880965219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3024652901395149920643479 4536979352092724880965219)
                ·
                  refine ⟨6805469028139087321447829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4536979352092724880965219 6805469028139087321447829)
                  ·
                    refine ⟨319006360694019718192867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6805469028139087321447829 319006360694019718192867)
                    ·
                      rfl

theorem cell23_1863788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 6].length) (baseStart_1863788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1863788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1863788 prefixEnd_1863788 := by exact prefixLift 1863788
  have htrace : WordTrace (prefixWord ++ tailWord_1863788) baseStart_1863788 baseEnd_1863788 := by
    simpa [prefixWord, tailWord_1863788, baseEnd_1863788] using wordTrace_append hprefix tailTrace_1863788
  have hstable : (prefixWord ++ tailWord_1863788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863788).length < 2 ^ (prefixWord ++ tailWord_1863788).sum := by decide
  have hdescent : baseEnd_1863788 < baseStart_1863788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863791 : List Nat := [1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 6]
def baseStart_1863791 : Nat := 118140960795 + 1863791 * 2 ^ 59
def prefixEnd_1863791 : Nat := 4983230072969 + 3 ^ 40 * 1863791 * 2
def baseEnd_1863791 : Nat := 957020622524022642841087

theorem tailTrace_1863791 : CollatzResearch.WordTrace tailWord_1863791 prefixEnd_1863791 957020622524022642841087 := by
  unfold tailWord_1863791
  simp only [CollatzResearch.WordTrace]
  refine ⟨67978042390810992005943227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45318694927207328003962151 67978042390810992005943227)
  ·
    refine ⟨101967063586216488008914841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67978042390810992005943227 101967063586216488008914841)
    ·
      refine ⟨76475297689662366006686131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101967063586216488008914841 76475297689662366006686131)
      ·
        refine ⟨114712946534493549010029197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76475297689662366006686131 114712946534493549010029197)
        ·
          refine ⟨43017354950435080878760949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114712946534493549010029197 43017354950435080878760949)
          ·
            refine ⟨4032877026603288832383839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43017354950435080878760949 4032877026603288832383839)
            ·
              refine ⟨6049315539904933248575759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4032877026603288832383839 6049315539904933248575759)
              ·
                refine ⟨9073973309857399872863639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6049315539904933248575759 9073973309857399872863639)
                ·
                  refine ⟨13610959964786099809295459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9073973309857399872863639 13610959964786099809295459)
                  ·
                    refine ⟨20416439947179149713943189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13610959964786099809295459 20416439947179149713943189)
                    ·
                      refine ⟨957020622524022642841087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20416439947179149713943189 957020622524022642841087)
                      ·
                        rfl

theorem cell23_1863791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 6].length) (baseStart_1863791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1863791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1863791 prefixEnd_1863791 := by exact prefixLift 1863791
  have htrace : WordTrace (prefixWord ++ tailWord_1863791) baseStart_1863791 baseEnd_1863791 := by
    simpa [prefixWord, tailWord_1863791, baseEnd_1863791] using wordTrace_append hprefix tailTrace_1863791
  have hstable : (prefixWord ++ tailWord_1863791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863791).length < 2 ^ (prefixWord ++ tailWord_1863791).sum := by decide
  have hdescent : baseEnd_1863791 < baseStart_1863791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863801 : List Nat := [1, 2, 1, 3, 4, 2, 1, 9]
def baseStart_1863801 : Nat := 118140960795 + 1863801 * 2 ^ 59
def prefixEnd_1863801 : Nat := 4983230072969 + 3 ^ 40 * 1863801 * 2
def baseEnd_1863801 : Nat := 35445398419650651989483

theorem tailTrace_1863801 : CollatzResearch.WordTrace tailWord_1863801 prefixEnd_1863801 35445398419650651989483 := by
  unfold tailWord_1863801
  simp only [CollatzResearch.WordTrace]
  refine ⟨67978407120774763713807257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45318938080516509142538171 67978407120774763713807257)
  ·
    refine ⟨50983805340581072785355443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67978407120774763713807257 50983805340581072785355443)
    ·
      refine ⟨76475708010871609178033165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50983805340581072785355443 76475708010871609178033165)
      ·
        refine ⟨28678390504076853441762437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76475708010871609178033165 28678390504076853441762437)
        ·
          refine ⟨5377198219514410020330457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28678390504076853441762437 5377198219514410020330457)
          ·
            refine ⟨4032898664635807515247843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5377198219514410020330457 4032898664635807515247843)
            ·
              refine ⟨6049347996953711272871765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4032898664635807515247843 6049347996953711272871765)
              ·
                refine ⟨35445398419650651989483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6049347996953711272871765 35445398419650651989483)
                ·
                  rfl

theorem cell23_1863801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 9].length) (baseStart_1863801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1863801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1863801 prefixEnd_1863801 := by exact prefixLift 1863801
  have htrace : WordTrace (prefixWord ++ tailWord_1863801) baseStart_1863801 baseEnd_1863801 := by
    simpa [prefixWord, tailWord_1863801, baseEnd_1863801] using wordTrace_append hprefix tailTrace_1863801
  have hstable : (prefixWord ++ tailWord_1863801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863801).length < 2 ^ (prefixWord ++ tailWord_1863801).sum := by decide
  have hdescent : baseEnd_1863801 < baseStart_1863801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863829 : List Nat := [1, 3, 2, 1, 1, 1, 7, 2, 1, 2, 2]
def baseStart_1863829 : Nat := 118140960795 + 1863829 * 2 ^ 59
def prefixEnd_1863829 : Nat := 4983230072969 + 3 ^ 40 * 1863829 * 2
def baseEnd_1863829 : Nat := 957040134788893494165913

theorem tailTrace_1863829 : CollatzResearch.WordTrace tailWord_1863829 prefixEnd_1863829 957040134788893494165913 := by
  unfold tailWord_1863829
  simp only [CollatzResearch.WordTrace]
  refine ⟨67979428364673324495826541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45319618909782216330551027 67979428364673324495826541)
  ·
    refine ⟨25492285636752496685934953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67979428364673324495826541 25492285636752496685934953)
    ·
      refine ⟨19119214227564372514451215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25492285636752496685934953 19119214227564372514451215)
      ·
        refine ⟨28678821341346558771676823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19119214227564372514451215 28678821341346558771676823)
        ·
          refine ⟨43018232012019838157515235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28678821341346558771676823 43018232012019838157515235)
          ·
            refine ⟨64527348018029757236272853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43018232012019838157515235 64527348018029757236272853)
            ·
              refine ⟨1512359719172572435225145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 64527348018029757236272853 1512359719172572435225145)
              ·
                refine ⟨1134269789379429326418859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1512359719172572435225145 1134269789379429326418859)
                ·
                  refine ⟨1701404684069143989628289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1134269789379429326418859 1701404684069143989628289)
                  ·
                    refine ⟨1276053513051857992221217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1701404684069143989628289 1276053513051857992221217)
                    ·
                      refine ⟨957040134788893494165913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1276053513051857992221217 957040134788893494165913)
                      ·
                        rfl

theorem cell23_1863829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7, 2, 1, 2, 2].length) (baseStart_1863829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1863829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1863829 prefixEnd_1863829 := by exact prefixLift 1863829
  have htrace : WordTrace (prefixWord ++ tailWord_1863829) baseStart_1863829 baseEnd_1863829 := by
    simpa [prefixWord, tailWord_1863829, baseEnd_1863829] using wordTrace_append hprefix tailTrace_1863829
  have hstable : (prefixWord ++ tailWord_1863829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863829).length < 2 ^ (prefixWord ++ tailWord_1863829).sum := by decide
  have hdescent : baseEnd_1863829 < baseStart_1863829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863845 : List Nat := [1, 3, 1, 2, 1, 3, 3, 3, 2, 1, 3]
def baseStart_1863845 : Nat := 118140960795 + 1863845 * 2 ^ 59
def prefixEnd_1863845 : Nat := 4983230072969 + 3 ^ 40 * 1863845 * 2
def baseEnd_1863845 : Nat := 957048350479365431565839

theorem tailTrace_1863845 : CollatzResearch.WordTrace tailWord_1863845 prefixEnd_1863845 957048350479365431565839 := by
  unfold tailWord_1863845
  simp only [CollatzResearch.WordTrace]
  refine ⟨67980011932615359228408989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45320007955076906152272659 67980011932615359228408989)
  ·
    refine ⟨25492504474730759710653371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67980011932615359228408989 25492504474730759710653371)
    ·
      refine ⟨38238756712096139565980057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25492504474730759710653371 38238756712096139565980057)
      ·
        refine ⟨28679067534072104674485043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38238756712096139565980057 28679067534072104674485043)
        ·
          refine ⟨43018601301108157011727565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28679067534072104674485043 43018601301108157011727565)
          ·
            refine ⟨16131975487915558879397837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43018601301108157011727565 16131975487915558879397837)
            ·
              refine ⟨6049490807968334579774189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16131975487915558879397837 6049490807968334579774189)
              ·
                refine ⟨2268559052988125467415321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6049490807968334579774189 2268559052988125467415321)
                ·
                  refine ⟨1701419289741094100561491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2268559052988125467415321 1701419289741094100561491)
                  ·
                    refine ⟨2552128934611641150842237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1701419289741094100561491 2552128934611641150842237)
                    ·
                      refine ⟨957048350479365431565839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2552128934611641150842237 957048350479365431565839)
                      ·
                        rfl

theorem cell23_1863845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 3, 2, 1, 3].length) (baseStart_1863845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1863845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1863845 prefixEnd_1863845 := by exact prefixLift 1863845
  have htrace : WordTrace (prefixWord ++ tailWord_1863845) baseStart_1863845 baseEnd_1863845 := by
    simpa [prefixWord, tailWord_1863845, baseEnd_1863845] using wordTrace_append hprefix tailTrace_1863845
  have hstable : (prefixWord ++ tailWord_1863845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863845).length < 2 ^ (prefixWord ++ tailWord_1863845).sum := by decide
  have hdescent : baseEnd_1863845 < baseStart_1863845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863918 : List Nat := [4, 1, 2, 1, 1, 1, 1, 1, 3, 5, 3]
def baseStart_1863918 : Nat := 118140960795 + 1863918 * 2 ^ 59
def prefixEnd_1863918 : Nat := 4983230072969 + 3 ^ 40 * 1863918 * 2
def baseEnd_1863918 : Nat := 957085834567143645953003

theorem tailTrace_1863918 : CollatzResearch.WordTrace tailWord_1863918 prefixEnd_1863918 957085834567143645953003 := by
  unfold tailWord_1863918
  simp only [CollatzResearch.WordTrace]
  refine ⟨8497834307668861586977051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45321782974233928463877605 8497834307668861586977051)
  ·
    refine ⟨12746751461503292380465577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8497834307668861586977051 12746751461503292380465577)
    ·
      refine ⟨9560063596127469285349183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12746751461503292380465577 9560063596127469285349183)
      ·
        refine ⟨14340095394191203928023775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9560063596127469285349183 14340095394191203928023775)
        ·
          refine ⟨21510143091286805892035663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14340095394191203928023775 21510143091286805892035663)
          ·
            refine ⟨32265214636930208838053495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21510143091286805892035663 32265214636930208838053495)
            ·
              refine ⟨48397821955395313257080243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32265214636930208838053495 48397821955395313257080243)
              ·
                refine ⟨72596732933092969885620365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48397821955395313257080243 72596732933092969885620365)
                ·
                  refine ⟨27223774849909863707107637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72596732933092969885620365 27223774849909863707107637)
                  ·
                    refine ⟨2552228892179049722541341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27223774849909863707107637 2552228892179049722541341)
                    ·
                      refine ⟨957085834567143645953003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2552228892179049722541341 957085834567143645953003)
                      ·
                        rfl

theorem cell23_1863918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_1863918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1863918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1863918 prefixEnd_1863918 := by exact prefixLift 1863918
  have htrace : WordTrace (prefixWord ++ tailWord_1863918) baseStart_1863918 baseEnd_1863918 := by
    simpa [prefixWord, tailWord_1863918, baseEnd_1863918] using wordTrace_append hprefix tailTrace_1863918
  have hstable : (prefixWord ++ tailWord_1863918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863918).length < 2 ^ (prefixWord ++ tailWord_1863918).sum := by decide
  have hdescent : baseEnd_1863918 < baseStart_1863918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864018 : List Nat := [3, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6]
def baseStart_1864018 : Nat := 118140960795 + 1864018 * 2 ^ 59
def prefixEnd_1864018 : Nat := 4983230072969 + 3 ^ 40 * 1864018 * 2
def baseEnd_1864018 : Nat := 957137182632593254702543

theorem tailTrace_1864018 : CollatzResearch.WordTrace tailWord_1864018 prefixEnd_1864018 957137182632593254702543 := by
  unfold tailWord_1864018
  simp only [CollatzResearch.WordTrace]
  refine ⟨16996580440247152443614177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45324214507325739849637805 16996580440247152443614177)
  ·
    refine ⟨12747435330185364332710633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16996580440247152443614177 12747435330185364332710633)
    ·
      refine ⟨9560576497639023249532975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12747435330185364332710633 9560576497639023249532975)
      ·
        refine ⟨14340864746458534874299463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9560576497639023249532975 14340864746458534874299463)
        ·
          refine ⟨21511297119687802311449195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14340864746458534874299463 21511297119687802311449195)
          ·
            refine ⟨32266945679531703467173793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21511297119687802311449195 32266945679531703467173793)
            ·
              refine ⟨24200209259648777600380345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32266945679531703467173793 24200209259648777600380345)
              ·
                refine ⟨18150156944736583200285259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24200209259648777600380345 18150156944736583200285259)
                ·
                  refine ⟨27225235417104874800427889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18150156944736583200285259 27225235417104874800427889)
                  ·
                    refine ⟨20418926562828656100320917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27225235417104874800427889 20418926562828656100320917)
                    ·
                      refine ⟨957137182632593254702543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20418926562828656100320917 957137182632593254702543)
                      ·
                        rfl

theorem cell23_1864018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_1864018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1864018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1864018 prefixEnd_1864018 := by exact prefixLift 1864018
  have htrace : WordTrace (prefixWord ++ tailWord_1864018) baseStart_1864018 baseEnd_1864018 := by
    simpa [prefixWord, tailWord_1864018, baseEnd_1864018] using wordTrace_append hprefix tailTrace_1864018
  have hstable : (prefixWord ++ tailWord_1864018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864018).length < 2 ^ (prefixWord ++ tailWord_1864018).sum := by decide
  have hdescent : baseEnd_1864018 < baseStart_1864018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864025 : List Nat := [1, 2, 1, 2, 2, 2, 1, 3, 5, 1, 3]
def baseStart_1864025 : Nat := 118140960795 + 1864025 * 2 ^ 59
def prefixEnd_1864025 : Nat := 4983230072969 + 3 ^ 40 * 1864025 * 2
def baseEnd_1864025 : Nat := 957140776997174727315011

theorem tailTrace_1864025 : CollatzResearch.WordTrace tailWord_1864025 prefixEnd_1864025 957140776997174727315011 := by
  unfold tailWord_1864025
  simp only [CollatzResearch.WordTrace]
  refine ⟨67986577071963249969961529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45324384714642166646641019 67986577071963249969961529)
  ·
    refine ⟨50989932803972437477471147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67986577071963249969961529 50989932803972437477471147)
    ·
      refine ⟨76484899205958656216206721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50989932803972437477471147 76484899205958656216206721)
      ·
        refine ⟨57363674404468992162155041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76484899205958656216206721 57363674404468992162155041)
        ·
          refine ⟨43022755803351744121616281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57363674404468992162155041 43022755803351744121616281)
          ·
            refine ⟨32267066852513808091212211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43022755803351744121616281 32267066852513808091212211)
            ·
              refine ⟨48400600278770712136818317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32267066852513808091212211 48400600278770712136818317)
              ·
                refine ⟨18150225104539017051306869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48400600278770712136818317 18150225104539017051306869)
                ·
                  refine ⟨1701583603550532848560019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18150225104539017051306869 1701583603550532848560019)
                  ·
                    refine ⟨2552375405325799272840029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1701583603550532848560019 2552375405325799272840029)
                    ·
                      refine ⟨957140776997174727315011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2552375405325799272840029 957140776997174727315011)
                      ·
                        rfl

theorem cell23_1864025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 5, 1, 3].length) (baseStart_1864025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1864025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1864025 prefixEnd_1864025 := by exact prefixLift 1864025
  have htrace : WordTrace (prefixWord ++ tailWord_1864025) baseStart_1864025 baseEnd_1864025 := by
    simpa [prefixWord, tailWord_1864025, baseEnd_1864025] using wordTrace_append hprefix tailTrace_1864025
  have hstable : (prefixWord ++ tailWord_1864025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864025).length < 2 ^ (prefixWord ++ tailWord_1864025).sum := by decide
  have hdescent : baseEnd_1864025 < baseStart_1864025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864059 : List Nat := [1, 1, 1, 1, 1, 8, 1, 4, 1, 1, 3]
def baseStart_1864059 : Nat := 118140960795 + 1864059 * 2 ^ 59
def prefixEnd_1864059 : Nat := 4983230072969 + 3 ^ 40 * 1864059 * 2
def baseEnd_1864059 : Nat := 957158235339427594289855

theorem tailTrace_1864059 : CollatzResearch.WordTrace tailWord_1864059 prefixEnd_1864059 957158235339427594289855 := by
  unfold tailWord_1864059
  simp only [CollatzResearch.WordTrace]
  refine ⟨67987817153840073776699231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45325211435893382517799487 67987817153840073776699231)
  ·
    refine ⟨101981725730760110665048847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67987817153840073776699231 101981725730760110665048847)
    ·
      refine ⟨152972588596140165997573271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101981725730760110665048847 152972588596140165997573271)
      ·
        refine ⟨229458882894210248996359907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152972588596140165997573271 229458882894210248996359907)
        ·
          refine ⟨344188324341315373494539861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229458882894210248996359907 344188324341315373494539861)
          ·
            refine ⟨4033456925874789533139139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 344188324341315373494539861 4033456925874789533139139)
            ·
              refine ⟨6050185388812184299708709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4033456925874789533139139 6050185388812184299708709)
              ·
                refine ⟨1134409760402284556195383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6050185388812184299708709 1134409760402284556195383)
                ·
                  refine ⟨1701614640603426834293075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1134409760402284556195383 1701614640603426834293075)
                  ·
                    refine ⟨2552421960905140251439613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1701614640603426834293075 2552421960905140251439613)
                    ·
                      refine ⟨957158235339427594289855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2552421960905140251439613 957158235339427594289855)
                      ·
                        rfl

theorem cell23_1864059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 4, 1, 1, 3].length) (baseStart_1864059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1864059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1864059 prefixEnd_1864059 := by exact prefixLift 1864059
  have htrace : WordTrace (prefixWord ++ tailWord_1864059) baseStart_1864059 baseEnd_1864059 := by
    simpa [prefixWord, tailWord_1864059, baseEnd_1864059] using wordTrace_append hprefix tailTrace_1864059
  have hstable : (prefixWord ++ tailWord_1864059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864059).length < 2 ^ (prefixWord ++ tailWord_1864059).sum := by decide
  have hdescent : baseEnd_1864059 < baseStart_1864059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864075 : List Nat := [1, 1, 1, 1, 4, 5, 2, 1, 1, 6]
def baseStart_1864075 : Nat := 118140960795 + 1864075 * 2 ^ 59
def prefixEnd_1864075 : Nat := 4983230072969 + 3 ^ 40 * 1864075 * 2
def baseEnd_1864075 : Nat := 319055483676633177229927

theorem tailTrace_1864075 : CollatzResearch.WordTrace tailWord_1864075 prefixEnd_1864075 319055483676633177229927 := by
  unfold tailWord_1864075
  simp only [CollatzResearch.WordTrace]
  refine ⟨67988400721782108509281679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45325600481188072339521119 67988400721782108509281679)
  ·
    refine ⟨101982601082673162763922519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67988400721782108509281679 101982601082673162763922519)
    ·
      refine ⟨152973901624009744145883779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101982601082673162763922519 152973901624009744145883779)
      ·
        refine ⟨229460852436014616218825669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152973901624009744145883779 229460852436014616218825669)
        ·
          refine ⟨43023909831752740541029813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 229460852436014616218825669 43023909831752740541029813)
          ·
            refine ⟨4033491546726819425721545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43023909831752740541029813 4033491546726819425721545)
            ·
              refine ⟨3025118660045114569291159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4033491546726819425721545 3025118660045114569291159)
              ·
                refine ⟨4537677990067671853936739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3025118660045114569291159 4537677990067671853936739)
                ·
                  refine ⟨6806516985101507780905109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4537677990067671853936739 6806516985101507780905109)
                  ·
                    refine ⟨319055483676633177229927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6806516985101507780905109 319055483676633177229927)
                    ·
                      rfl

theorem cell23_1864075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 1, 1, 6].length) (baseStart_1864075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1864075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1864075 prefixEnd_1864075 := by exact prefixLift 1864075
  have htrace : WordTrace (prefixWord ++ tailWord_1864075) baseStart_1864075 baseEnd_1864075 := by
    simpa [prefixWord, tailWord_1864075, baseEnd_1864075] using wordTrace_append hprefix tailTrace_1864075
  have hstable : (prefixWord ++ tailWord_1864075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864075).length < 2 ^ (prefixWord ++ tailWord_1864075).sum := by decide
  have hdescent : baseEnd_1864075 < baseStart_1864075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864095 : List Nat := [1, 1, 2, 5, 1, 1, 1, 4, 1, 2, 4]
def baseStart_1864095 : Nat := 118140960795 + 1864095 * 2 ^ 59
def prefixEnd_1864095 : Nat := 4983230072969 + 3 ^ 40 * 1864095 * 2
def baseEnd_1864095 : Nat := 957176720642989453439689

theorem tailTrace_1864095 : CollatzResearch.WordTrace tailWord_1864095 prefixEnd_1864095 957176720642989453439689 := by
  unfold tailWord_1864095
  simp only [CollatzResearch.WordTrace]
  refine ⟨67989130181709651925009739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45326086787806434616673159 67989130181709651925009739)
  ·
    refine ⟨101983695272564477887514609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67989130181709651925009739 101983695272564477887514609)
    ·
      refine ⟨76487771454423358415635957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101983695272564477887514609 76487771454423358415635957)
      ·
        refine ⟨7170728573852189851465871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76487771454423358415635957 7170728573852189851465871)
        ·
          refine ⟨10756092860778284777198807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7170728573852189851465871 10756092860778284777198807)
          ·
            refine ⟨16134139291167427165798211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10756092860778284777198807 16134139291167427165798211)
            ·
              refine ⟨24201208936751140748697317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16134139291167427165798211 24201208936751140748697317)
              ·
                refine ⟨4537726675640838890380747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24201208936751140748697317 4537726675640838890380747)
                ·
                  refine ⟨6806590013461258335571121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4537726675640838890380747 6806590013461258335571121)
                  ·
                    refine ⟨5104942510095943751678341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6806590013461258335571121 5104942510095943751678341)
                    ·
                      refine ⟨957176720642989453439689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5104942510095943751678341 957176720642989453439689)
                      ·
                        rfl

theorem cell23_1864095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_1864095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1864095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1864095 prefixEnd_1864095 := by exact prefixLift 1864095
  have htrace : WordTrace (prefixWord ++ tailWord_1864095) baseStart_1864095 baseEnd_1864095 := by
    simpa [prefixWord, tailWord_1864095, baseEnd_1864095] using wordTrace_append hprefix tailTrace_1864095
  have hstable : (prefixWord ++ tailWord_1864095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864095).length < 2 ^ (prefixWord ++ tailWord_1864095).sum := by decide
  have hdescent : baseEnd_1864095 < baseStart_1864095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864099 : List Nat := [1, 1, 1, 4, 1, 6, 2, 1, 1, 1, 4]
def baseStart_1864099 : Nat := 118140960795 + 1864099 * 2 ^ 59
def prefixEnd_1864099 : Nat := 4983230072969 + 3 ^ 40 * 1864099 * 2
def baseEnd_1864099 : Nat := 957178774565607437789671

theorem tailTrace_1864099 : CollatzResearch.WordTrace tailWord_1864099 prefixEnd_1864099 957178774565607437789671 := by
  unfold tailWord_1864099
  simp only [CollatzResearch.WordTrace]
  refine ⟨67989276073695160608155351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45326184049130107072103567 67989276073695160608155351)
  ·
    refine ⟨101983914110542740912233027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67989276073695160608155351 101983914110542740912233027)
    ·
      refine ⟨152975871165814111368349541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101983914110542740912233027 152975871165814111368349541)
      ·
        refine ⟨28682975843590145881565539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152975871165814111368349541 28682975843590145881565539)
        ·
          refine ⟨43024463765385218822348309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28682975843590145881565539 43024463765385218822348309)
          ·
            refine ⟨2016771739002432132297577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 43024463765385218822348309 2016771739002432132297577)
            ·
              refine ⟨1512578804251824099223183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2016771739002432132297577 1512578804251824099223183)
              ·
                refine ⟨2268868206377736148834775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1512578804251824099223183 2268868206377736148834775)
                ·
                  refine ⟨3403302309566604223252163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2268868206377736148834775 3403302309566604223252163)
                  ·
                    refine ⟨5104953464349906334878245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3403302309566604223252163 5104953464349906334878245)
                    ·
                      refine ⟨957178774565607437789671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5104953464349906334878245 957178774565607437789671)
                      ·
                        rfl

theorem cell23_1864099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2, 1, 1, 1, 4].length) (baseStart_1864099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1864099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1864099 prefixEnd_1864099 := by exact prefixLift 1864099
  have htrace : WordTrace (prefixWord ++ tailWord_1864099) baseStart_1864099 baseEnd_1864099 := by
    simpa [prefixWord, tailWord_1864099, baseEnd_1864099] using wordTrace_append hprefix tailTrace_1864099
  have hstable : (prefixWord ++ tailWord_1864099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864099).length < 2 ^ (prefixWord ++ tailWord_1864099).sum := by decide
  have hdescent : baseEnd_1864099 < baseStart_1864099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864108 : List Nat := [2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 6]
def baseStart_1864108 : Nat := 118140960795 + 1864108 * 2 ^ 59
def prefixEnd_1864108 : Nat := 4983230072969 + 3 ^ 40 * 1864108 * 2
def baseEnd_1864108 : Nat := 957183395891497902577129

theorem tailTrace_1864108 : CollatzResearch.WordTrace tailWord_1864108 prefixEnd_1864108 957183395891497902577129 := by
  unfold tailWord_1864108
  simp only [CollatzResearch.WordTrace]
  refine ⟨33994802165331277572616489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45326402887108370096821985 33994802165331277572616489)
  ·
    refine ⟨25496101623998458179462367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33994802165331277572616489 25496101623998458179462367)
    ·
      refine ⟨38244152435997687269193551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25496101623998458179462367 38244152435997687269193551)
      ·
        refine ⟨57366228653996530903790327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38244152435997687269193551 57366228653996530903790327)
        ·
          refine ⟨86049342980994796355685491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57366228653996530903790327 86049342980994796355685491)
          ·
            refine ⟨129074014471492194533528237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86049342980994796355685491 129074014471492194533528237)
            ·
              refine ⟨48402755426809572950073089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129074014471492194533528237 48402755426809572950073089)
              ·
                refine ⟨36302066570107179712554817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48402755426809572950073089 36302066570107179712554817)
                ·
                  refine ⟨27226549927580384784416113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36302066570107179712554817 27226549927580384784416113)
                  ·
                    refine ⟨20419912445685288588312085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27226549927580384784416113 20419912445685288588312085)
                    ·
                      refine ⟨957183395891497902577129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20419912445685288588312085 957183395891497902577129)
                      ·
                        rfl

theorem cell23_1864108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 6].length) (baseStart_1864108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1864108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1864108 prefixEnd_1864108 := by exact prefixLift 1864108
  have htrace : WordTrace (prefixWord ++ tailWord_1864108) baseStart_1864108 baseEnd_1864108 := by
    simpa [prefixWord, tailWord_1864108, baseEnd_1864108] using wordTrace_append hprefix tailTrace_1864108
  have hstable : (prefixWord ++ tailWord_1864108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864108).length < 2 ^ (prefixWord ++ tailWord_1864108).sum := by decide
  have hdescent : baseEnd_1864108 < baseStart_1864108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864109 : List Nat := [1, 5, 2, 2, 2, 1, 1, 1, 4, 4]
def baseStart_1864109 : Nat := 118140960795 + 1864109 * 2 ^ 59
def prefixEnd_1864109 : Nat := 4983230072969 + 3 ^ 40 * 1864109 * 2
def baseEnd_1864109 : Nat := 319061303124050799554875

theorem tailTrace_1864109 : CollatzResearch.WordTrace tailWord_1864109 prefixEnd_1864109 319061303124050799554875 := by
  unfold tailWord_1864109
  simp only [CollatzResearch.WordTrace]
  refine ⟨67989640803658932316019381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45326427202439288210679587 67989640803658932316019381)
  ·
    refine ⟨6374028825343024904626817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67989640803658932316019381 6374028825343024904626817)
    ·
      refine ⟨4780521619007268678470113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6374028825343024904626817 4780521619007268678470113)
      ·
        refine ⟨3585391214255451508852585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4780521619007268678470113 3585391214255451508852585)
        ·
          refine ⟨2689043410691588631639439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3585391214255451508852585 2689043410691588631639439)
          ·
            refine ⟨4033565116037382947459159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2689043410691588631639439 4033565116037382947459159)
            ·
              refine ⟨6050347674056074421188739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4033565116037382947459159 6050347674056074421188739)
              ·
                refine ⟨9075521511084111631783109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6050347674056074421188739 9075521511084111631783109)
                ·
                  refine ⟨1701660283328270930959333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9075521511084111631783109 1701660283328270930959333)
                  ·
                    refine ⟨319061303124050799554875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1701660283328270930959333 319061303124050799554875)
                    ·
                      rfl

theorem cell23_1864109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_1864109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1864109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1864109 prefixEnd_1864109 := by exact prefixLift 1864109
  have htrace : WordTrace (prefixWord ++ tailWord_1864109) baseStart_1864109 baseEnd_1864109 := by
    simpa [prefixWord, tailWord_1864109, baseEnd_1864109] using wordTrace_append hprefix tailTrace_1864109
  have hstable : (prefixWord ++ tailWord_1864109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864109).length < 2 ^ (prefixWord ++ tailWord_1864109).sum := by decide
  have hdescent : baseEnd_1864109 < baseStart_1864109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864159 : List Nat := [1, 1, 2, 3, 3, 2, 2, 3, 1, 3, 2]
def baseStart_1864159 : Nat := 118140960795 + 1864159 * 2 ^ 59
def prefixEnd_1864159 : Nat := 4983230072969 + 3 ^ 40 * 1864159 * 2
def baseEnd_1864159 : Nat := 957209583404877203039395

theorem tailTrace_1864159 : CollatzResearch.WordTrace tailWord_1864159 prefixEnd_1864159 957209583404877203039395 := by
  unfold tailWord_1864159
  simp only [CollatzResearch.WordTrace]
  refine ⟨67991464453477790855339531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45327642968985193903559687 67991464453477790855339531)
  ·
    refine ⟨101987196680216686283009297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67991464453477790855339531 101987196680216686283009297)
    ·
      refine ⟨76490397510162514712256973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101987196680216686283009297 76490397510162514712256973)
      ·
        refine ⟨28683899066310943017096365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76490397510162514712256973 28683899066310943017096365)
        ·
          refine ⟨10756462149866603631411137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28683899066310943017096365 10756462149866603631411137)
          ·
            refine ⟨8067346612399952723558353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10756462149866603631411137 8067346612399952723558353)
            ·
              refine ⟨6050509959299964542668765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8067346612399952723558353 6050509959299964542668765)
              ·
                refine ⟨2268941234737486703500787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6050509959299964542668765 2268941234737486703500787)
                ·
                  refine ⟨3403411852106230055251181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2268941234737486703500787 3403411852106230055251181)
                  ·
                    refine ⟨1276279444539836270719193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3403411852106230055251181 1276279444539836270719193)
                    ·
                      refine ⟨957209583404877203039395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1276279444539836270719193 957209583404877203039395)
                      ·
                        rfl

theorem cell23_1864159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 3, 1, 3, 2].length) (baseStart_1864159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1864159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1864159 prefixEnd_1864159 := by exact prefixLift 1864159
  have htrace : WordTrace (prefixWord ++ tailWord_1864159) baseStart_1864159 baseEnd_1864159 := by
    simpa [prefixWord, tailWord_1864159, baseEnd_1864159] using wordTrace_append hprefix tailTrace_1864159
  have hstable : (prefixWord ++ tailWord_1864159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864159).length < 2 ^ (prefixWord ++ tailWord_1864159).sum := by decide
  have hdescent : baseEnd_1864159 < baseStart_1864159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864175 : List Nat := [1, 1, 2, 1, 4, 1, 1, 3, 2, 4, 3]
def baseStart_1864175 : Nat := 118140960795 + 1864175 * 2 ^ 59
def prefixEnd_1864175 : Nat := 4983230072969 + 3 ^ 40 * 1864175 * 2
def baseEnd_1864175 : Nat := 957217799095349140439321

theorem tailTrace_1864175 : CollatzResearch.WordTrace tailWord_1864175 prefixEnd_1864175 957217799095349140439321 := by
  unfold tailWord_1864175
  simp only [CollatzResearch.WordTrace]
  refine ⟨67992048021419825587921979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45328032014279883725281319 67992048021419825587921979)
  ·
    refine ⟨101988072032129738381882969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67992048021419825587921979 101988072032129738381882969)
    ·
      refine ⟨76491054024097303786412227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101988072032129738381882969 76491054024097303786412227)
      ·
        refine ⟨114736581036145955679618341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76491054024097303786412227 114736581036145955679618341)
        ·
          refine ⟨21513108944277366689928439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114736581036145955679618341 21513108944277366689928439)
          ·
            refine ⟨32269663416416050034892659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21513108944277366689928439 32269663416416050034892659)
            ·
              refine ⟨48404495124624075052338989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32269663416416050034892659 48404495124624075052338989)
              ·
                refine ⟨18151685671734028144627121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48404495124624075052338989 18151685671734028144627121)
                ·
                  refine ⟨13613764253800521108470341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18151685671734028144627121 13613764253800521108470341)
                  ·
                    refine ⟨2552580797587597707838189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13613764253800521108470341 2552580797587597707838189)
                    ·
                      refine ⟨957217799095349140439321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2552580797587597707838189 957217799095349140439321)
                      ·
                        rfl

theorem cell23_1864175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 4, 3].length) (baseStart_1864175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1864175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1864175 prefixEnd_1864175 := by exact prefixLift 1864175
  have htrace : WordTrace (prefixWord ++ tailWord_1864175) baseStart_1864175 baseEnd_1864175 := by
    simpa [prefixWord, tailWord_1864175, baseEnd_1864175] using wordTrace_append hprefix tailTrace_1864175
  have hstable : (prefixWord ++ tailWord_1864175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864175).length < 2 ^ (prefixWord ++ tailWord_1864175).sum := by decide
  have hdescent : baseEnd_1864175 < baseStart_1864175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864185 : List Nat := [1, 2, 1, 3, 1, 2, 2, 3, 2, 2, 4]
def baseStart_1864185 : Nat := 118140960795 + 1864185 * 2 ^ 59
def prefixEnd_1864185 : Nat := 4983230072969 + 3 ^ 40 * 1864185 * 2
def baseEnd_1864185 : Nat := 957222933901894101314275

theorem tailTrace_1864185 : CollatzResearch.WordTrace tailWord_1864185 prefixEnd_1864185 957222933901894101314275 := by
  unfold tailWord_1864185
  simp only [CollatzResearch.WordTrace]
  refine ⟨67992412751383597295786009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45328275167589064863857339 67992412751383597295786009)
  ·
    refine ⟨50994309563537697971839507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67992412751383597295786009 50994309563537697971839507)
    ·
      refine ⟨76491464345306546957759261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50994309563537697971839507 76491464345306546957759261)
      ·
        refine ⟨28684299129489955109159723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76491464345306546957759261 28684299129489955109159723)
        ·
          refine ⟨43026448694234932663739585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28684299129489955109159723 43026448694234932663739585)
          ·
            refine ⟨32269836520676199497804689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43026448694234932663739585 32269836520676199497804689)
            ·
              refine ⟨24202377390507149623353517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32269836520676199497804689 24202377390507149623353517)
              ·
                refine ⟨9075891521440181108757569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24202377390507149623353517 9075891521440181108757569)
                ·
                  refine ⟨6806918641080135831568177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9075891521440181108757569 6806918641080135831568177)
                  ·
                    refine ⟨5105188980810101873676133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6806918641080135831568177 5105188980810101873676133)
                    ·
                      refine ⟨957222933901894101314275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5105188980810101873676133 957222933901894101314275)
                      ·
                        rfl

theorem cell23_1864185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_1864185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1864185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1864185 prefixEnd_1864185 := by exact prefixLift 1864185
  have htrace : WordTrace (prefixWord ++ tailWord_1864185) baseStart_1864185 baseEnd_1864185 := by
    simpa [prefixWord, tailWord_1864185, baseEnd_1864185] using wordTrace_append hprefix tailTrace_1864185
  have hstable : (prefixWord ++ tailWord_1864185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864185).length < 2 ^ (prefixWord ++ tailWord_1864185).sum := by decide
  have hdescent : baseEnd_1864185 < baseStart_1864185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864229 : List Nat := [1, 3, 1, 2, 2, 1, 6, 2, 5]
def baseStart_1864229 : Nat := 118140960795 + 1864229 * 2 ^ 59
def prefixEnd_1864229 : Nat := 4983230072969 + 3 ^ 40 * 1864229 * 2
def baseEnd_1864229 : Nat := 106360614116743547684897

theorem tailTrace_1864229 : CollatzResearch.WordTrace tailWord_1864229 prefixEnd_1864229 106360614116743547684897 := by
  unfold tailWord_1864229
  simp only [CollatzResearch.WordTrace]
  refine ⟨67994017563224192810387741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45329345042149461873591827 67994017563224192810387741)
  ·
    refine ⟨25497756586209072303895403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67994017563224192810387741 25497756586209072303895403)
    ·
      refine ⟨38246634879313608455843105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25497756586209072303895403 38246634879313608455843105)
      ·
        refine ⟨28684976159485206341882329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38246634879313608455843105 28684976159485206341882329)
        ·
          refine ⟨21513732119613904756411747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28684976159485206341882329 21513732119613904756411747)
          ·
            refine ⟨32270598179420857134617621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21513732119613904756411747 32270598179420857134617621)
            ·
              refine ⟨1512684289660352678185201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 32270598179420857134617621 1512684289660352678185201)
              ·
                refine ⟨1134513217245264508638901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1512684289660352678185201 1134513217245264508638901)
                ·
                  refine ⟨106360614116743547684897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1134513217245264508638901 106360614116743547684897)
                  ·
                    rfl

theorem cell23_1864229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6, 2, 5].length) (baseStart_1864229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1864229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1864229 prefixEnd_1864229 := by exact prefixLift 1864229
  have htrace : WordTrace (prefixWord ++ tailWord_1864229) baseStart_1864229 baseEnd_1864229 := by
    simpa [prefixWord, tailWord_1864229, baseEnd_1864229] using wordTrace_append hprefix tailTrace_1864229
  have hstable : (prefixWord ++ tailWord_1864229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864229).length < 2 ^ (prefixWord ++ tailWord_1864229).sum := by decide
  have hdescent : baseEnd_1864229 < baseStart_1864229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864289 : List Nat := [1, 2, 3, 1, 1, 5, 2, 1, 3, 4]
def baseStart_1864289 : Nat := 118140960795 + 1864289 * 2 ^ 59
def prefixEnd_1864289 : Nat := 4983230072969 + 3 ^ 40 * 1864289 * 2
def baseEnd_1864289 : Nat := 319092111963320564804599

theorem tailTrace_1864289 : CollatzResearch.WordTrace tailWord_1864289 prefixEnd_1864289 319092111963320564804599 := by
  unfold tailWord_1864289
  simp only [CollatzResearch.WordTrace]
  refine ⟨67996205943006823057571921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45330803962004548705047947 67996205943006823057571921)
  ·
    refine ⟨50997154457255117293178941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67996205943006823057571921 50997154457255117293178941)
    ·
      refine ⟨19123932921470668984942103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50997154457255117293178941 19123932921470668984942103)
      ·
        refine ⟨28685899382206003477413155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19123932921470668984942103 28685899382206003477413155)
        ·
          refine ⟨43028849073309005216119733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28685899382206003477413155 43028849073309005216119733)
          ·
            refine ⟨4033954600622719239011225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43028849073309005216119733 4033954600622719239011225)
            ·
              refine ⟨3025465950467039429258419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4033954600622719239011225 3025465950467039429258419)
              ·
                refine ⟨4538198925700559143887629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3025465950467039429258419 4538198925700559143887629)
                ·
                  refine ⟨1701824597137709678957861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4538198925700559143887629 1701824597137709678957861)
                  ·
                    refine ⟨319092111963320564804599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1701824597137709678957861 319092111963320564804599)
                    ·
                      rfl

theorem cell23_1864289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 1, 3, 4].length) (baseStart_1864289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1864289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1864289 prefixEnd_1864289 := by exact prefixLift 1864289
  have htrace : WordTrace (prefixWord ++ tailWord_1864289) baseStart_1864289 baseEnd_1864289 := by
    simpa [prefixWord, tailWord_1864289, baseEnd_1864289] using wordTrace_append hprefix tailTrace_1864289
  have hstable : (prefixWord ++ tailWord_1864289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864289).length < 2 ^ (prefixWord ++ tailWord_1864289).sum := by decide
  have hdescent : baseEnd_1864289 < baseStart_1864289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864339 : List Nat := [1, 1, 1, 2, 1, 2, 2, 6, 2, 3, 2]
def baseStart_1864339 : Nat := 118140960795 + 1864339 * 2 ^ 59
def prefixEnd_1864339 : Nat := 4983230072969 + 3 ^ 40 * 1864339 * 2
def baseEnd_1864339 : Nat := 957302009922686498788567

theorem tailTrace_1864339 : CollatzResearch.WordTrace tailWord_1864339 prefixEnd_1864339 957302009922686498788567 := by
  unfold tailWord_1864339
  simp only [CollatzResearch.WordTrace]
  refine ⟨67998029592825681596892071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45332019728550454397928047 67998029592825681596892071)
  ·
    refine ⟨101997044389238522395338107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67998029592825681596892071 101997044389238522395338107)
    ·
      refine ⟨152995566583857783593007161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101997044389238522395338107 152995566583857783593007161)
      ·
        refine ⟨114746674937893337694755371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152995566583857783593007161 114746674937893337694755371)
        ·
          refine ⟨172120012406840006542133057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114746674937893337694755371 172120012406840006542133057)
          ·
            refine ⟨129090009305130004906599793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172120012406840006542133057 129090009305130004906599793)
            ·
              refine ⟨96817506978847503679949845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129090009305130004906599793 96817506978847503679949845)
              ·
                refine ⟨4538320639633476734997649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 96817506978847503679949845 4538320639633476734997649)
                ·
                  refine ⟨3403740479725107551248237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4538320639633476734997649 3403740479725107551248237)
                  ·
                    refine ⟨1276402679896915331718089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3403740479725107551248237 1276402679896915331718089)
                    ·
                      refine ⟨957302009922686498788567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1276402679896915331718089 957302009922686498788567)
                      ·
                        rfl

theorem cell23_1864339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6, 2, 3, 2].length) (baseStart_1864339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1864339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1864339 prefixEnd_1864339 := by exact prefixLift 1864339
  have htrace : WordTrace (prefixWord ++ tailWord_1864339) baseStart_1864339 baseEnd_1864339 := by
    simpa [prefixWord, tailWord_1864339, baseEnd_1864339] using wordTrace_append hprefix tailTrace_1864339
  have hstable : (prefixWord ++ tailWord_1864339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864339).length < 2 ^ (prefixWord ++ tailWord_1864339).sum := by decide
  have hdescent : baseEnd_1864339 < baseStart_1864339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864340 : List Nat := [2, 4, 2, 2, 1, 2, 3, 2, 1, 4]
def baseStart_1864340 : Nat := 118140960795 + 1864340 * 2 ^ 59
def prefixEnd_1864340 : Nat := 4983230072969 + 3 ^ 40 * 1864340 * 2
def baseEnd_1864340 : Nat := 319100841134446998292021

theorem tailTrace_1864340 : CollatzResearch.WordTrace tailWord_1864340 prefixEnd_1864340 319100841134446998292021 := by
  unfold tailWord_1864340
  simp only [CollatzResearch.WordTrace]
  refine ⟨33999033032911029383839237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45332044043881372511785649 33999033032911029383839237)
  ·
    refine ⟨6374818693670818009469857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33999033032911029383839237 6374818693670818009469857)
    ·
      refine ⟨4781114020253113507102393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6374818693670818009469857 4781114020253113507102393)
      ·
        refine ⟨3585835515189835130326795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4781114020253113507102393 3585835515189835130326795)
        ·
          refine ⟨5378753272784752695490193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3585835515189835130326795 5378753272784752695490193)
          ·
            refine ⟨4034064954588564521617645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5378753272784752695490193 4034064954588564521617645)
            ·
              refine ⟨1512774357970711695606617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4034064954588564521617645 1512774357970711695606617)
              ·
                refine ⟨1134580768478033771704963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1512774357970711695606617 1134580768478033771704963)
                ·
                  refine ⟨1701871152717050657557445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1134580768478033771704963 1701871152717050657557445)
                  ·
                    refine ⟨319100841134446998292021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1701871152717050657557445 319100841134446998292021)
                    ·
                      rfl

theorem cell23_1864340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_1864340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1864340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1864340 prefixEnd_1864340 := by exact prefixLift 1864340
  have htrace : WordTrace (prefixWord ++ tailWord_1864340) baseStart_1864340 baseEnd_1864340 := by
    simpa [prefixWord, tailWord_1864340, baseEnd_1864340] using wordTrace_append hprefix tailTrace_1864340
  have hstable : (prefixWord ++ tailWord_1864340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864340).length < 2 ^ (prefixWord ++ tailWord_1864340).sum := by decide
  have hdescent : baseEnd_1864340 < baseStart_1864340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864353 : List Nat := [1, 2, 3, 3, 4, 1, 2, 1, 6]
def baseStart_1864353 : Nat := 118140960795 + 1864353 * 2 ^ 59
def prefixEnd_1864353 : Nat := 4983230072969 + 3 ^ 40 * 1864353 * 2
def baseEnd_1864353 : Nat := 106367688739094382668167

theorem tailTrace_1864353 : CollatzResearch.WordTrace tailWord_1864353 prefixEnd_1864353 106367688739094382668167 := by
  unfold tailWord_1864353
  simp only [CollatzResearch.WordTrace]
  refine ⟨67998540214774961987901713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45332360143183307991934475 67998540214774961987901713)
  ·
    refine ⟨50998905161081221490926285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67998540214774961987901713 50998905161081221490926285)
    ·
      refine ⟨19124589435405458059097357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50998905161081221490926285 19124589435405458059097357)
      ·
        refine ⟨7171721038277046772161509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19124589435405458059097357 7171721038277046772161509)
        ·
          refine ⟨1344697694676946269780283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7171721038277046772161509 1344697694676946269780283)
          ·
            refine ⟨2017046542015419404670425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1344697694676946269780283 2017046542015419404670425)
            ·
              refine ⟨1512784906511564553502819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2017046542015419404670425 1512784906511564553502819)
              ·
                refine ⟨2269177359767346830254229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1512784906511564553502819 2269177359767346830254229)
                ·
                  refine ⟨106367688739094382668167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2269177359767346830254229 106367688739094382668167)
                  ·
                    rfl

theorem cell23_1864353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 2, 1, 6].length) (baseStart_1864353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1864353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1864353 prefixEnd_1864353 := by exact prefixLift 1864353
  have htrace : WordTrace (prefixWord ++ tailWord_1864353) baseStart_1864353 baseEnd_1864353 := by
    simpa [prefixWord, tailWord_1864353, baseEnd_1864353] using wordTrace_append hprefix tailTrace_1864353
  have hstable : (prefixWord ++ tailWord_1864353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864353).length < 2 ^ (prefixWord ++ tailWord_1864353).sum := by decide
  have hdescent : baseEnd_1864353 < baseStart_1864353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864366 : List Nat := [4, 1, 4, 1, 1, 2, 1, 1, 3, 5]
def baseStart_1864366 : Nat := 118140960795 + 1864366 * 2 ^ 59
def prefixEnd_1864366 : Nat := 4983230072969 + 3 ^ 40 * 1864366 * 2
def baseEnd_1864366 : Nat := 319105291300119297716981

theorem tailTrace_1864366 : CollatzResearch.WordTrace tailWord_1864366 prefixEnd_1864366 319105291300119297716981 := by
  unfold tailWord_1864366
  simp only [CollatzResearch.WordTrace]
  refine ⟨8499876795465983151015619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45332676242485243472083301 8499876795465983151015619)
  ·
    refine ⟨12749815193198974726523429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8499876795465983151015619 12749815193198974726523429)
    ·
      refine ⟨2390590348724807761223143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12749815193198974726523429 2390590348724807761223143)
      ·
        refine ⟨3585885523087211641834715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2390590348724807761223143 3585885523087211641834715)
        ·
          refine ⟨5378828284630817462752073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3585885523087211641834715 5378828284630817462752073)
          ·
            refine ⟨4034121213473113097064055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5378828284630817462752073 4034121213473113097064055)
            ·
              refine ⟨6051181820209669645596083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4034121213473113097064055 6051181820209669645596083)
              ·
                refine ⟨9076772730314504468394125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6051181820209669645596083 9076772730314504468394125)
                ·
                  refine ⟨3403789773867939175647797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9076772730314504468394125 3403789773867939175647797)
                  ·
                    refine ⟨319105291300119297716981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3403789773867939175647797 319105291300119297716981)
                    ·
                      rfl

theorem cell23_1864366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_1864366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1864366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1864366 prefixEnd_1864366 := by exact prefixLift 1864366
  have htrace : WordTrace (prefixWord ++ tailWord_1864366) baseStart_1864366 baseEnd_1864366 := by
    simpa [prefixWord, tailWord_1864366, baseEnd_1864366] using wordTrace_append hprefix tailTrace_1864366
  have hstable : (prefixWord ++ tailWord_1864366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864366).length < 2 ^ (prefixWord ++ tailWord_1864366).sum := by decide
  have hdescent : baseEnd_1864366 < baseStart_1864366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864373 : List Nat := [1, 3, 3, 3, 1, 2, 2, 1, 2, 3, 2]
def baseStart_1864373 : Nat := 118140960795 + 1864373 * 2 ^ 59
def prefixEnd_1864373 : Nat := 4983230072969 + 3 ^ 40 * 1864373 * 2
def baseEnd_1864373 : Nat := 957319468264939365763411

theorem tailTrace_1864373 : CollatzResearch.WordTrace tailWord_1864373 prefixEnd_1864373 957319468264939365763411 := by
  unfold tailWord_1864373
  simp only [CollatzResearch.WordTrace]
  refine ⟨67999269674702505403629773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45332846449801670269086515 67999269674702505403629773)
  ·
    refine ⟨25499726128013439526361165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67999269674702505403629773 25499726128013439526361165)
    ·
      refine ⟨9562397298005039822385437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25499726128013439526361165 9562397298005039822385437)
      ·
        refine ⟨3585898986751889933394539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9562397298005039822385437 3585898986751889933394539)
        ·
          refine ⟨5378848480127834900091809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3585898986751889933394539 5378848480127834900091809)
          ·
            refine ⟨4034136360095876175068857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5378848480127834900091809 4034136360095876175068857)
            ·
              refine ⟨3025602270071907131301643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4034136360095876175068857 3025602270071907131301643)
              ·
                refine ⟨4538403405107860696952465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3025602270071907131301643 4538403405107860696952465)
                ·
                  refine ⟨3403802553830895522714349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4538403405107860696952465 3403802553830895522714349)
                  ·
                    refine ⟨1276425957686585821017881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3403802553830895522714349 1276425957686585821017881)
                    ·
                      refine ⟨957319468264939365763411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1276425957686585821017881 957319468264939365763411)
                      ·
                        rfl

theorem cell23_1864373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_1864373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1864373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1864373 prefixEnd_1864373 := by exact prefixLift 1864373
  have htrace : WordTrace (prefixWord ++ tailWord_1864373) baseStart_1864373 baseEnd_1864373 := by
    simpa [prefixWord, tailWord_1864373, baseEnd_1864373] using wordTrace_append hprefix tailTrace_1864373
  have hstable : (prefixWord ++ tailWord_1864373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864373).length < 2 ^ (prefixWord ++ tailWord_1864373).sum := by decide
  have hdescent : baseEnd_1864373 < baseStart_1864373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864396 : List Nat := [2, 2, 1, 5, 1, 1, 1, 4, 2, 4]
def baseStart_1864396 : Nat := 118140960795 + 1864396 * 2 ^ 59
def prefixEnd_1864396 : Nat := 4983230072969 + 3 ^ 40 * 1864396 * 2
def baseEnd_1864396 : Nat := 319110426106664258591935

theorem tailTrace_1864396 : CollatzResearch.WordTrace tailWord_1864396 prefixEnd_1864396 319110426106664258591935 := by
  unfold tailWord_1864396
  simp only [CollatzResearch.WordTrace]
  refine ⟨34000054276809590165858521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45333405702412786887811361 34000054276809590165858521)
  ·
    refine ⟨25500040707607192624393891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34000054276809590165858521 25500040707607192624393891)
    ·
      refine ⟨38250061061410788936590837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25500040707607192624393891 38250061061410788936590837)
      ·
        refine ⟨3585943224507261462805391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38250061061410788936590837 3585943224507261462805391)
        ·
          refine ⟨5378914836760892194208087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3585943224507261462805391 5378914836760892194208087)
          ·
            refine ⟨8068372255141338291312131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5378914836760892194208087 8068372255141338291312131)
            ·
              refine ⟨12102558382712007436968197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8068372255141338291312131 12102558382712007436968197)
              ·
                refine ⟨2269229696758501394431537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12102558382712007436968197 2269229696758501394431537)
                ·
                  refine ⟨1701922272568876045823653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2269229696758501394431537 1701922272568876045823653)
                  ·
                    refine ⟨319110426106664258591935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1701922272568876045823653 319110426106664258591935)
                    ·
                      rfl

theorem cell23_1864396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 4, 2, 4].length) (baseStart_1864396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1864396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1864396 prefixEnd_1864396 := by exact prefixLift 1864396
  have htrace : WordTrace (prefixWord ++ tailWord_1864396) baseStart_1864396 baseEnd_1864396 := by
    simpa [prefixWord, tailWord_1864396, baseEnd_1864396] using wordTrace_append hprefix tailTrace_1864396
  have hstable : (prefixWord ++ tailWord_1864396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864396).length < 2 ^ (prefixWord ++ tailWord_1864396).sum := by decide
  have hdescent : baseEnd_1864396 < baseStart_1864396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864397 : List Nat := [1, 6, 2, 1, 2, 1, 1, 4, 1, 1, 3]
def baseStart_1864397 : Nat := 118140960795 + 1864397 * 2 ^ 59
def prefixEnd_1864397 : Nat := 4983230072969 + 3 ^ 40 * 1864397 * 2
def baseEnd_1864397 : Nat := 957331791800647271863301

theorem tailTrace_1864397 : CollatzResearch.WordTrace tailWord_1864397 prefixEnd_1864397 957331791800647271863301 := by
  unfold tailWord_1864397
  simp only [CollatzResearch.WordTrace]
  refine ⟨68000145026615557502503445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45333430017743705001668963 68000145026615557502503445)
  ·
    refine ⟨3187506798122604257929849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 68000145026615557502503445 3187506798122604257929849)
    ·
      refine ⟨2390630098591953193447387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3187506798122604257929849 2390630098591953193447387)
      ·
        refine ⟨3585945147887929790171081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2390630098591953193447387 3585945147887929790171081)
        ·
          refine ⟨2689458860915947342628311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3585945147887929790171081 2689458860915947342628311)
          ·
            refine ⟨4034188291373921013942467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2689458860915947342628311 4034188291373921013942467)
            ·
              refine ⟨6051282437060881520913701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4034188291373921013942467 6051282437060881520913701)
              ·
                refine ⟨1134615456948915285171319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6051282437060881520913701 1134615456948915285171319)
                ·
                  refine ⟨1701923185423372927756979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1134615456948915285171319 1701923185423372927756979)
                  ·
                    refine ⟨2552884778135059391635469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1701923185423372927756979 2552884778135059391635469)
                    ·
                      refine ⟨957331791800647271863301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2552884778135059391635469 957331791800647271863301)
                      ·
                        rfl

theorem cell23_1864397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_1864397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1864397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1864397 prefixEnd_1864397 := by exact prefixLift 1864397
  have htrace : WordTrace (prefixWord ++ tailWord_1864397) baseStart_1864397 baseEnd_1864397 := by
    simpa [prefixWord, tailWord_1864397, baseEnd_1864397] using wordTrace_append hprefix tailTrace_1864397
  have hstable : (prefixWord ++ tailWord_1864397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864397).length < 2 ^ (prefixWord ++ tailWord_1864397).sum := by decide
  have hdescent : baseEnd_1864397 < baseStart_1864397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864432 : List Nat := [2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 5]
def baseStart_1864432 : Nat := 118140960795 + 1864432 * 2 ^ 59
def prefixEnd_1864432 : Nat := 4983230072969 + 3 ^ 40 * 1864432 * 2
def baseEnd_1864432 : Nat := 957349763623554634925639

theorem tailTrace_1864432 : CollatzResearch.WordTrace tailWord_1864432 prefixEnd_1864432 957349763623554634925639 := by
  unfold tailWord_1864432
  simp only [CollatzResearch.WordTrace]
  refine ⟨34000710790744379240013775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45334281054325838986685033 34000710790744379240013775)
  ·
    refine ⟨51001066186116568860020663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34000710790744379240013775 51001066186116568860020663)
    ·
      refine ⟨76501599279174853290030995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51001066186116568860020663 76501599279174853290030995)
      ·
        refine ⟨114752398918762279935046493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76501599279174853290030995 114752398918762279935046493)
        ·
          refine ⟨43032149594535854975642435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114752398918762279935046493 43032149594535854975642435)
          ·
            refine ⟨64548224391803782463463653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43032149594535854975642435 64548224391803782463463653)
            ·
              refine ⟨12102792073463209211899435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64548224391803782463463653 12102792073463209211899435)
              ·
                refine ⟨18154188110194813817849153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12102792073463209211899435 18154188110194813817849153)
                ·
                  refine ⟨13615641082646110363386865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18154188110194813817849153 13615641082646110363386865)
                  ·
                    refine ⟨10211730811984582772540149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13615641082646110363386865 10211730811984582772540149)
                    ·
                      refine ⟨957349763623554634925639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10211730811984582772540149 957349763623554634925639)
                      ·
                        rfl

theorem cell23_1864432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 5].length) (baseStart_1864432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1864432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1864432 prefixEnd_1864432 := by exact prefixLift 1864432
  have htrace : WordTrace (prefixWord ++ tailWord_1864432) baseStart_1864432 baseEnd_1864432 := by
    simpa [prefixWord, tailWord_1864432, baseEnd_1864432] using wordTrace_append hprefix tailTrace_1864432
  have hstable : (prefixWord ++ tailWord_1864432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864432).length < 2 ^ (prefixWord ++ tailWord_1864432).sum := by decide
  have hdescent : baseEnd_1864432 < baseStart_1864432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864549 : List Nat := [1, 3, 1, 3, 1, 1, 2, 3, 1, 3, 4]
def baseStart_1864549 : Nat := 118140960795 + 1864549 * 2 ^ 59
def prefixEnd_1864549 : Nat := 4983230072969 + 3 ^ 40 * 1864549 * 2
def baseEnd_1864549 : Nat := 957409840860130677162601

theorem tailTrace_1864549 : CollatzResearch.WordTrace tailWord_1864549 prefixEnd_1864549 957409840860130677162601 := by
  unfold tailWord_1864549
  simp only [CollatzResearch.WordTrace]
  refine ⟨68005688922064887462036701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45337125948043258308024467 68005688922064887462036701)
  ·
    refine ⟨25502133345774332798263763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68005688922064887462036701 25502133345774332798263763)
    ·
      refine ⟨38253200018661499197395645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25502133345774332798263763 38253200018661499197395645)
      ·
        refine ⟨14344950006998062199023367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38253200018661499197395645 14344950006998062199023367)
        ·
          refine ⟨21517425010497093298535051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14344950006998062199023367 21517425010497093298535051)
          ·
            refine ⟨32276137515745639947802577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21517425010497093298535051 32276137515745639947802577)
            ·
              refine ⟨24207103136809229960851933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32276137515745639947802577 24207103136809229960851933)
              ·
                refine ⟨9077663676303461235319475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24207103136809229960851933 9077663676303461235319475)
                ·
                  refine ⟨13616495514455191852979213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9077663676303461235319475 13616495514455191852979213)
                  ·
                    refine ⟨5106185817920696944867205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13616495514455191852979213 5106185817920696944867205)
                    ·
                      refine ⟨957409840860130677162601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5106185817920696944867205 957409840860130677162601)
                      ·
                        rfl

theorem cell23_1864549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_1864549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1864549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1864549 prefixEnd_1864549 := by exact prefixLift 1864549
  have htrace : WordTrace (prefixWord ++ tailWord_1864549) baseStart_1864549 baseEnd_1864549 := by
    simpa [prefixWord, tailWord_1864549, baseEnd_1864549] using wordTrace_append hprefix tailTrace_1864549
  have hstable : (prefixWord ++ tailWord_1864549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864549).length < 2 ^ (prefixWord ++ tailWord_1864549).sum := by decide
  have hdescent : baseEnd_1864549 < baseStart_1864549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864583 : List Nat := [1, 1, 4, 2, 3, 2, 1, 1, 2, 4, 2]
def baseStart_1864583 : Nat := 118140960795 + 1864583 * 2 ^ 59
def prefixEnd_1864583 : Nat := 4983230072969 + 3 ^ 40 * 1864583 * 2
def baseEnd_1864583 : Nat := 957427299202383544137445

theorem tailTrace_1864583 : CollatzResearch.WordTrace tailWord_1864583 prefixEnd_1864583 957427299202383544137445 := by
  unfold tailWord_1864583
  simp only [CollatzResearch.WordTrace]
  refine ⟨68006929003941711268774403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45337952669294474179182935 68006929003941711268774403)
  ·
    refine ⟨102010393505912566903161605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68006929003941711268774403 102010393505912566903161605)
    ·
      refine ⟨19126948782358606294342801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102010393505912566903161605 19126948782358606294342801)
      ·
        refine ⟨14345211586768954720757101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19126948782358606294342801 14345211586768954720757101)
        ·
          refine ⟨5379454345038358020283913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14345211586768954720757101 5379454345038358020283913)
          ·
            refine ⟨4034590758778768515212935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5379454345038358020283913 4034590758778768515212935)
            ·
              refine ⟨6051886138168152772819403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4034590758778768515212935 6051886138168152772819403)
              ·
                refine ⟨9077829207252229159229105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6051886138168152772819403 9077829207252229159229105)
                ·
                  refine ⟨6808371905439171869421829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9077829207252229159229105 6808371905439171869421829)
                  ·
                    refine ⟨1276569732269844725516593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6808371905439171869421829 1276569732269844725516593)
                    ·
                      refine ⟨957427299202383544137445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1276569732269844725516593 957427299202383544137445)
                      ·
                        rfl

theorem cell23_1864583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 2, 4, 2].length) (baseStart_1864583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1864583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1864583 prefixEnd_1864583 := by exact prefixLift 1864583
  have htrace : WordTrace (prefixWord ++ tailWord_1864583) baseStart_1864583 baseEnd_1864583 := by
    simpa [prefixWord, tailWord_1864583, baseEnd_1864583] using wordTrace_append hprefix tailTrace_1864583
  have hstable : (prefixWord ++ tailWord_1864583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864583).length < 2 ^ (prefixWord ++ tailWord_1864583).sum := by decide
  have hdescent : baseEnd_1864583 < baseStart_1864583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864610 : List Nat := [3, 3, 1, 2, 2, 1, 1, 5, 1, 4]
def baseStart_1864610 : Nat := 118140960795 + 1864610 * 2 ^ 59
def prefixEnd_1864610 : Nat := 4983230072969 + 3 ^ 40 * 1864610 * 2
def baseEnd_1864610 : Nat := 319147054393351646166607

theorem tailTrace_1864610 : CollatzResearch.WordTrace tailWord_1864610 prefixEnd_1864610 319147054393351646166607 := by
  unfold tailWord_1864610
  simp only [CollatzResearch.WordTrace]
  refine ⟨17001978443710973720001821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45338609183229263253338189 17001978443710973720001821)
  ·
    refine ⟨6375741916391615145000683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17001978443710973720001821 6375741916391615145000683)
    ·
      refine ⟨9563612874587422717501025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6375741916391615145000683 9563612874587422717501025)
      ·
        refine ⟨7172709655940567038125769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9563612874587422717501025 7172709655940567038125769)
        ·
          refine ⟨5379532241955425278594327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7172709655940567038125769 5379532241955425278594327)
          ·
            refine ⟨8069298362933137917891491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5379532241955425278594327 8069298362933137917891491)
            ·
              refine ⟨12103947544399706876837237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8069298362933137917891491 12103947544399706876837237)
              ·
                refine ⟨1134745082287472519703491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12103947544399706876837237 1134745082287472519703491)
                ·
                  refine ⟨1702117623431208779555237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1134745082287472519703491 1702117623431208779555237)
                  ·
                    refine ⟨319147054393351646166607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1702117623431208779555237 319147054393351646166607)
                    ·
                      rfl

theorem cell23_1864610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 5, 1, 4].length) (baseStart_1864610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1864610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1864610 prefixEnd_1864610 := by exact prefixLift 1864610
  have htrace : WordTrace (prefixWord ++ tailWord_1864610) baseStart_1864610 baseEnd_1864610 := by
    simpa [prefixWord, tailWord_1864610, baseEnd_1864610] using wordTrace_append hprefix tailTrace_1864610
  have hstable : (prefixWord ++ tailWord_1864610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864610).length < 2 ^ (prefixWord ++ tailWord_1864610).sum := by decide
  have hdescent : baseEnd_1864610 < baseStart_1864610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864633 : List Nat := [1, 2, 1, 4, 2, 2, 1, 3, 3, 1, 3]
def baseStart_1864633 : Nat := 118140960795 + 1864633 * 2 ^ 59
def prefixEnd_1864633 : Nat := 4983230072969 + 3 ^ 40 * 1864633 * 2
def baseEnd_1864633 : Nat := 957452973235108348512215

theorem tailTrace_1864633 : CollatzResearch.WordTrace tailWord_1864633 prefixEnd_1864633 957452973235108348512215 := by
  unfold tailWord_1864633
  simp only [CollatzResearch.WordTrace]
  refine ⟨68008752653760569808094553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45339168435840379872063035 68008752653760569808094553)
  ·
    refine ⟨51006564490320427356070915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68008752653760569808094553 51006564490320427356070915)
    ·
      refine ⟨76509846735480641034106373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51006564490320427356070915 76509846735480641034106373)
      ·
        refine ⟨14345596262902620193894945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76509846735480641034106373 14345596262902620193894945)
        ·
          refine ⟨10759197197176965145421209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14345596262902620193894945 10759197197176965145421209)
          ·
            refine ⟨8069397897882723859065907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10759197197176965145421209 8069397897882723859065907)
            ·
              refine ⟨12104096846824085788598861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8069397897882723859065907 12104096846824085788598861)
              ·
                refine ⟨4539036317559032170724573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12104096846824085788598861 4539036317559032170724573)
                ·
                  refine ⟨1702138619084637064021715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4539036317559032170724573 1702138619084637064021715)
                  ·
                    refine ⟨2553207928626955596032573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1702138619084637064021715 2553207928626955596032573)
                    ·
                      refine ⟨957452973235108348512215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2553207928626955596032573 957452973235108348512215)
                      ·
                        rfl

theorem cell23_1864633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 3, 3, 1, 3].length) (baseStart_1864633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1864633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1864633 prefixEnd_1864633 := by exact prefixLift 1864633
  have htrace : WordTrace (prefixWord ++ tailWord_1864633) baseStart_1864633 baseEnd_1864633 := by
    simpa [prefixWord, tailWord_1864633, baseEnd_1864633] using wordTrace_append hprefix tailTrace_1864633
  have hstable : (prefixWord ++ tailWord_1864633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864633).length < 2 ^ (prefixWord ++ tailWord_1864633).sum := by decide
  have hdescent : baseEnd_1864633 < baseStart_1864633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864639 : List Nat := [1, 1, 2, 2, 2, 1, 2, 1, 2, 5, 4]
def baseStart_1864639 : Nat := 118140960795 + 1864639 * 2 ^ 59
def prefixEnd_1864639 : Nat := 4983230072969 + 3 ^ 40 * 1864639 * 2
def baseEnd_1864639 : Nat := 957456054119035325037187

theorem tailTrace_1864639 : CollatzResearch.WordTrace tailWord_1864639 prefixEnd_1864639 957456054119035325037187 := by
  unfold tailWord_1864639
  simp only [CollatzResearch.WordTrace]
  refine ⟨68008971491738832832812971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45339314327825888555208647 68008971491738832832812971)
  ·
    refine ⟨102013457237608249249219457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68008971491738832832812971 102013457237608249249219457)
    ·
      refine ⟨76510092928206186936914593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102013457237608249249219457 76510092928206186936914593)
      ·
        refine ⟨57382569696154640202685945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76510092928206186936914593 57382569696154640202685945)
        ·
          refine ⟨43036927272115980152014459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57382569696154640202685945 43036927272115980152014459)
          ·
            refine ⟨64555390908173970228021689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43036927272115980152014459 64555390908173970228021689)
            ·
              refine ⟨48416543181130477671016267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64555390908173970228021689 48416543181130477671016267)
              ·
                refine ⟨72624814771695716506524401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48416543181130477671016267 72624814771695716506524401)
                ·
                  refine ⟨54468611078771787379893301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72624814771695716506524401 54468611078771787379893301)
                  ·
                    refine ⟨5106432288634855066864997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54468611078771787379893301 5106432288634855066864997)
                    ·
                      refine ⟨957456054119035325037187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5106432288634855066864997 957456054119035325037187)
                      ·
                        rfl

theorem cell23_1864639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 5, 4].length) (baseStart_1864639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1864639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1864639 prefixEnd_1864639 := by exact prefixLift 1864639
  have htrace : WordTrace (prefixWord ++ tailWord_1864639) baseStart_1864639 baseEnd_1864639 := by
    simpa [prefixWord, tailWord_1864639, baseEnd_1864639] using wordTrace_append hprefix tailTrace_1864639
  have hstable : (prefixWord ++ tailWord_1864639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864639).length < 2 ^ (prefixWord ++ tailWord_1864639).sum := by decide
  have hdescent : baseEnd_1864639 < baseStart_1864639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864656 : List Nat := [2, 1, 1, 1, 1, 2, 3, 1, 1, 8, 2]
def baseStart_1864656 : Nat := 118140960795 + 1864656 * 2 ^ 59
def prefixEnd_1864656 : Nat := 4983230072969 + 3 ^ 40 * 1864656 * 2
def baseEnd_1864656 : Nat := 957464783290161758524609

theorem tailTrace_1864656 : CollatzResearch.WordTrace tailWord_1864656 prefixEnd_1864656 957464783290161758524609 := by
  unfold tailWord_1864656
  simp only [CollatzResearch.WordTrace]
  refine ⟨34004795766338622368090911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45339727688451496490787881 34004795766338622368090911)
  ·
    refine ⟨51007193649507933552136367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34004795766338622368090911 51007193649507933552136367)
    ·
      refine ⟨76510790474261900328204551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51007193649507933552136367 76510790474261900328204551)
      ·
        refine ⟨114766185711392850492306827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76510790474261900328204551 114766185711392850492306827)
        ·
          refine ⟨172149278567089275738460241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114766185711392850492306827 172149278567089275738460241)
          ·
            refine ⟨129111958925316956803845181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172149278567089275738460241 129111958925316956803845181)
            ·
              refine ⟨48416984596993858801441943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129111958925316956803845181 48416984596993858801441943)
              ·
                refine ⟨72625476895490788202162915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48416984596993858801441943 72625476895490788202162915)
                ·
                  refine ⟨108938215343236182303244373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72625476895490788202162915 108938215343236182303244373)
                  ·
                    refine ⟨1276619711053549011366145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 108938215343236182303244373 1276619711053549011366145)
                    ·
                      refine ⟨957464783290161758524609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1276619711053549011366145 957464783290161758524609)
                      ·
                        rfl

theorem cell23_1864656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 1, 8, 2].length) (baseStart_1864656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1864656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1864656 prefixEnd_1864656 := by exact prefixLift 1864656
  have htrace : WordTrace (prefixWord ++ tailWord_1864656) baseStart_1864656 baseEnd_1864656 := by
    simpa [prefixWord, tailWord_1864656, baseEnd_1864656] using wordTrace_append hprefix tailTrace_1864656
  have hstable : (prefixWord ++ tailWord_1864656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864656).length < 2 ^ (prefixWord ++ tailWord_1864656).sum := by decide
  have hdescent : baseEnd_1864656 < baseStart_1864656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864677 : List Nat := [1, 3, 1, 6, 1, 1, 1, 2, 2, 3, 2]
def baseStart_1864677 : Nat := 118140960795 + 1864677 * 2 ^ 59
def prefixEnd_1864677 : Nat := 4983230072969 + 3 ^ 40 * 1864677 * 2
def baseEnd_1864677 : Nat := 957475566383906176362013

theorem tailTrace_1864677 : CollatzResearch.WordTrace tailWord_1864677 prefixEnd_1864677 957475566383906176362013 := by
  unfold tailWord_1864677
  simp only [CollatzResearch.WordTrace]
  refine ⟨68010357465601165322696285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45340238310400776881797523 68010357465601165322696285)
  ·
    refine ⟨25503884049600436996011107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68010357465601165322696285 25503884049600436996011107)
    ·
      refine ⟨38255826074400655494016661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25503884049600436996011107 38255826074400655494016661)
      ·
        refine ⟨1793241847237530726282031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 38255826074400655494016661 1793241847237530726282031)
        ·
          refine ⟨2689862770856296089423047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1793241847237530726282031 2689862770856296089423047)
          ·
            refine ⟨4034794156284444134134571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2689862770856296089423047 4034794156284444134134571)
            ·
              refine ⟨6052191234426666201201857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4034794156284444134134571 6052191234426666201201857)
              ·
                refine ⟨4539143425819999650901393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6052191234426666201201857 4539143425819999650901393)
                ·
                  refine ⟨3404357569364999738176045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4539143425819999650901393 3404357569364999738176045)
                  ·
                    refine ⟨1276634088511874901816017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3404357569364999738176045 1276634088511874901816017)
                    ·
                      refine ⟨957475566383906176362013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1276634088511874901816017 957475566383906176362013)
                      ·
                        rfl

theorem cell23_1864677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_1864677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1864677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1864677 prefixEnd_1864677 := by exact prefixLift 1864677
  have htrace : WordTrace (prefixWord ++ tailWord_1864677) baseStart_1864677 baseEnd_1864677 := by
    simpa [prefixWord, tailWord_1864677, baseEnd_1864677] using wordTrace_append hprefix tailTrace_1864677
  have hstable : (prefixWord ++ tailWord_1864677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864677).length < 2 ^ (prefixWord ++ tailWord_1864677).sum := by decide
  have hdescent : baseEnd_1864677 < baseStart_1864677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864699 : List Nat := [1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 6]
def baseStart_1864699 : Nat := 118140960795 + 1864699 * 2 ^ 59
def prefixEnd_1864699 : Nat := 4983230072969 + 3 ^ 40 * 1864699 * 2
def baseEnd_1864699 : Nat := 957486862958305090286911

theorem tailTrace_1864699 : CollatzResearch.WordTrace tailWord_1864699 prefixEnd_1864699 957486862958305090286911 := by
  unfold tailWord_1864699
  simp only [CollatzResearch.WordTrace]
  refine ⟨68011159871521463079997151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45340773247680975386664767 68011159871521463079997151)
  ·
    refine ⟨102016739807282194619995727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68011159871521463079997151 102016739807282194619995727)
    ·
      refine ⟨153025109710923291929993591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102016739807282194619995727 153025109710923291929993591)
      ·
        refine ⟨229537664566384937894990387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153025109710923291929993591 229537664566384937894990387)
        ·
          refine ⟨344306496849577406842485581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229537664566384937894990387 344306496849577406842485581)
          ·
            refine ⟨129114936318591527565932093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 344306496849577406842485581 129114936318591527565932093)
            ·
              refine ⟨48418101119471822837224535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129114936318591527565932093 48418101119471822837224535)
              ·
                refine ⟨72627151679207734255836803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48418101119471822837224535 72627151679207734255836803)
                ·
                  refine ⟨108940727518811601383755205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72627151679207734255836803 108940727518811601383755205)
                  ·
                    refine ⟨20426386409777175259454101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 108940727518811601383755205 20426386409777175259454101)
                    ·
                      refine ⟨957486862958305090286911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20426386409777175259454101 957486862958305090286911)
                      ·
                        rfl

theorem cell23_1864699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 6].length) (baseStart_1864699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1864699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1864699 prefixEnd_1864699 := by exact prefixLift 1864699
  have htrace : WordTrace (prefixWord ++ tailWord_1864699) baseStart_1864699 baseEnd_1864699 := by
    simpa [prefixWord, tailWord_1864699, baseEnd_1864699] using wordTrace_append hprefix tailTrace_1864699
  have hstable : (prefixWord ++ tailWord_1864699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864699).length < 2 ^ (prefixWord ++ tailWord_1864699).sum := by decide
  have hdescent : baseEnd_1864699 < baseStart_1864699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864700 : List Nat := [2, 2, 2, 1, 2, 3, 4, 1, 2, 4]
def baseStart_1864700 : Nat := 118140960795 + 1864700 * 2 ^ 59
def prefixEnd_1864700 : Nat := 4983230072969 + 3 ^ 40 * 1864700 * 2
def baseEnd_1864700 : Nat := 319162458812986528791469

theorem tailTrace_1864700 : CollatzResearch.WordTrace tailWord_1864700 prefixEnd_1864700 319162458812986528791469 := by
  unfold tailWord_1864700
  simp only [CollatzResearch.WordTrace]
  refine ⟨34005598172258920125391777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45340797563011893500522369 34005598172258920125391777)
  ·
    refine ⟨25504198629194190094043833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34005598172258920125391777 25504198629194190094043833)
    ·
      refine ⟨19128148971895642570532875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25504198629194190094043833 19128148971895642570532875)
      ·
        refine ⟨28692223457843463855799313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19128148971895642570532875 28692223457843463855799313)
        ·
          refine ⟨21519167593382597891849485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28692223457843463855799313 21519167593382597891849485)
          ·
            refine ⟨8069687847518474209443557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21519167593382597891849485 8069687847518474209443557)
            ·
              refine ⟨1513066471409713914270667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8069687847518474209443557 1513066471409713914270667)
              ·
                refine ⟨2269599707114570871406001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1513066471409713914270667 2269599707114570871406001)
                ·
                  refine ⟨1702199780335928153554501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2269599707114570871406001 1702199780335928153554501)
                  ·
                    refine ⟨319162458812986528791469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1702199780335928153554501 319162458812986528791469)
                    ·
                      rfl

theorem cell23_1864700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4, 1, 2, 4].length) (baseStart_1864700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1864700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1864700 prefixEnd_1864700 := by exact prefixLift 1864700
  have htrace : WordTrace (prefixWord ++ tailWord_1864700) baseStart_1864700 baseEnd_1864700 := by
    simpa [prefixWord, tailWord_1864700, baseEnd_1864700] using wordTrace_append hprefix tailTrace_1864700
  have hstable : (prefixWord ++ tailWord_1864700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864700).length < 2 ^ (prefixWord ++ tailWord_1864700).sum := by decide
  have hdescent : baseEnd_1864700 < baseStart_1864700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864727 : List Nat := [1, 1, 3, 5, 1, 2, 3, 1, 1, 2, 3]
def baseStart_1864727 : Nat := 118140960795 + 1864727 * 2 ^ 59
def prefixEnd_1864727 : Nat := 4983230072969 + 3 ^ 40 * 1864727 * 2
def baseEnd_1864727 : Nat := 957501240416630980736783

theorem tailTrace_1864727 : CollatzResearch.WordTrace tailWord_1864727 prefixEnd_1864727 957501240416630980736783 := by
  unfold tailWord_1864727
  simp only [CollatzResearch.WordTrace]
  refine ⟨68012181115420023862016435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45341454076946682574677623 68012181115420023862016435)
  ·
    refine ⟨102018271673130035793024653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68012181115420023862016435 102018271673130035793024653)
    ·
      refine ⟨38256851877423763422384245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102018271673130035793024653 38256851877423763422384245)
      ·
        refine ⟨3586579863508477820848523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38256851877423763422384245 3586579863508477820848523)
        ·
          refine ⟨5379869795262716731272785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3586579863508477820848523 5379869795262716731272785)
          ·
            refine ⟨4034902346447037548454589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5379869795262716731272785 4034902346447037548454589)
            ·
              refine ⟨1513088379917639080670471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4034902346447037548454589 1513088379917639080670471)
              ·
                refine ⟨2269632569876458621005707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1513088379917639080670471 2269632569876458621005707)
                ·
                  refine ⟨3404448854814687931508561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2269632569876458621005707 3404448854814687931508561)
                  ·
                    refine ⟨2553336641111015948631421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3404448854814687931508561 2553336641111015948631421)
                    ·
                      refine ⟨957501240416630980736783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2553336641111015948631421 957501240416630980736783)
                      ·
                        rfl

theorem cell23_1864727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_1864727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1864727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1864727 prefixEnd_1864727 := by exact prefixLift 1864727
  have htrace : WordTrace (prefixWord ++ tailWord_1864727) baseStart_1864727 baseEnd_1864727 := by
    simpa [prefixWord, tailWord_1864727, baseEnd_1864727] using wordTrace_append hprefix tailTrace_1864727
  have hstable : (prefixWord ++ tailWord_1864727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864727).length < 2 ^ (prefixWord ++ tailWord_1864727).sum := by decide
  have hdescent : baseEnd_1864727 < baseStart_1864727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864743 : List Nat := [1, 1, 7, 1, 1, 1, 1, 1, 2, 7]
def baseStart_1864743 : Nat := 118140960795 + 1864743 * 2 ^ 59
def prefixEnd_1864743 : Nat := 4983230072969 + 3 ^ 40 * 1864743 * 2
def baseEnd_1864743 : Nat := 319169818702367639378903

theorem tailTrace_1864743 : CollatzResearch.WordTrace tailWord_1864743 prefixEnd_1864743 319169818702367639378903 := by
  unfold tailWord_1864743
  simp only [CollatzResearch.WordTrace]
  refine ⟨68012764683362058594598883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45341843122241372396399255 68012764683362058594598883)
  ·
    refine ⟨102019147025043087891898325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68012764683362058594598883 102019147025043087891898325)
    ·
      refine ⟨2391073758399447372466367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 102019147025043087891898325 2391073758399447372466367)
      ·
        refine ⟨3586610637599171058699551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2391073758399447372466367 3586610637599171058699551)
        ·
          refine ⟨5379915956398756588049327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3586610637599171058699551 5379915956398756588049327)
          ·
            refine ⟨8069873934598134882073991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5379915956398756588049327 8069873934598134882073991)
            ·
              refine ⟨12104810901897202323110987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8069873934598134882073991 12104810901897202323110987)
              ·
                refine ⟨18157216352845803484666481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12104810901897202323110987 18157216352845803484666481)
                ·
                  refine ⟨13617912264634352613499861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18157216352845803484666481 13617912264634352613499861)
                  ·
                    refine ⟨319169818702367639378903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13617912264634352613499861 319169818702367639378903)
                    ·
                      rfl

theorem cell23_1864743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_1864743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1864743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1864743 prefixEnd_1864743 := by exact prefixLift 1864743
  have htrace : WordTrace (prefixWord ++ tailWord_1864743) baseStart_1864743 baseEnd_1864743 := by
    simpa [prefixWord, tailWord_1864743, baseEnd_1864743] using wordTrace_append hprefix tailTrace_1864743
  have hstable : (prefixWord ++ tailWord_1864743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864743).length < 2 ^ (prefixWord ++ tailWord_1864743).sum := by decide
  have hdescent : baseEnd_1864743 < baseStart_1864743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864750 : List Nat := [4, 1, 3, 1, 1, 1, 1, 1, 5, 3, 2]
def baseStart_1864750 : Nat := 118140960795 + 1864750 * 2 ^ 59
def prefixEnd_1864750 : Nat := 4983230072969 + 3 ^ 40 * 1864750 * 2
def baseEnd_1864750 : Nat := 957513050471684390749177

theorem tailTrace_1864750 : CollatzResearch.WordTrace tailWord_1864750 prefixEnd_1864750 957513050471684390749177 := by
  unfold tailWord_1864750
  simp only [CollatzResearch.WordTrace]
  refine ⟨8501627499292087348762963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45342013329557799193402469 8501627499292087348762963)
  ·
    refine ⟨12752441248938131023144445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8501627499292087348762963 12752441248938131023144445)
    ·
      refine ⟨4782165468351799133679167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12752441248938131023144445 4782165468351799133679167)
      ·
        refine ⟨7173248202527698700518751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4782165468351799133679167 7173248202527698700518751)
        ·
          refine ⟨10759872303791548050778127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7173248202527698700518751 10759872303791548050778127)
          ·
            refine ⟨16139808455687322076167191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10759872303791548050778127 16139808455687322076167191)
            ·
              refine ⟨24209712683530983114250787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16139808455687322076167191 24209712683530983114250787)
              ·
                refine ⟨36314569025296474671376181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24209712683530983114250787 36314569025296474671376181)
                ·
                  refine ⟨3404490846121544500441517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36314569025296474671376181 3404490846121544500441517)
                  ·
                    refine ⟨1276684067295579187665569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3404490846121544500441517 1276684067295579187665569)
                    ·
                      refine ⟨957513050471684390749177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1276684067295579187665569 957513050471684390749177)
                      ·
                        rfl

theorem cell23_1864750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_1864750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1864750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1864750 prefixEnd_1864750 := by exact prefixLift 1864750
  have htrace : WordTrace (prefixWord ++ tailWord_1864750) baseStart_1864750 baseEnd_1864750 := by
    simpa [prefixWord, tailWord_1864750, baseEnd_1864750] using wordTrace_append hprefix tailTrace_1864750
  have hstable : (prefixWord ++ tailWord_1864750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864750).length < 2 ^ (prefixWord ++ tailWord_1864750).sum := by decide
  have hdescent : baseEnd_1864750 < baseStart_1864750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864776 : List Nat := [2, 1, 3, 1, 1, 1, 3, 2, 1, 4, 4]
def baseStart_1864776 : Nat := 118140960795 + 1864776 * 2 ^ 59
def prefixEnd_1864776 : Nat := 4983230072969 + 3 ^ 40 * 1864776 * 2
def baseEnd_1864776 : Nat := 957526400968701289024057

theorem tailTrace_1864776 : CollatzResearch.WordTrace tailWord_1864776 prefixEnd_1864776 957526400968701289024057 := by
  unfold tailWord_1864776
  simp only [CollatzResearch.WordTrace]
  refine ⟨34006984146121252615275091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45342645528161670153700121 34006984146121252615275091)
  ·
    refine ⟨51010476219181878922912637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34006984146121252615275091 51010476219181878922912637)
    ·
      refine ⟨19128928582193204596092239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51010476219181878922912637 19128928582193204596092239)
      ·
        refine ⟨28693392873289806894138359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19128928582193204596092239 28693392873289806894138359)
        ·
          refine ⟨43040089309934710341207539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28693392873289806894138359 43040089309934710341207539)
          ·
            refine ⟨64560133964902065511811309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43040089309934710341207539 64560133964902065511811309)
            ·
              refine ⟨24210050236838274566929241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64560133964902065511811309 24210050236838274566929241)
              ·
                refine ⟨18157537677628705925196931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24210050236838274566929241 18157537677628705925196931)
                ·
                  refine ⟨27236306516443058887795397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18157537677628705925196931 27236306516443058887795397)
                  ·
                    refine ⟨5106807471833073541461637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27236306516443058887795397 5106807471833073541461637)
                    ·
                      refine ⟨957526400968701289024057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5106807471833073541461637 957526400968701289024057)
                      ·
                        rfl

theorem cell23_1864776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_1864776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1864776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1864776 prefixEnd_1864776 := by exact prefixLift 1864776
  have htrace : WordTrace (prefixWord ++ tailWord_1864776) baseStart_1864776 baseEnd_1864776 := by
    simpa [prefixWord, tailWord_1864776, baseEnd_1864776] using wordTrace_append hprefix tailTrace_1864776
  have hstable : (prefixWord ++ tailWord_1864776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864776).length < 2 ^ (prefixWord ++ tailWord_1864776).sum := by decide
  have hdescent : baseEnd_1864776 < baseStart_1864776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864780 : List Nat := [2, 2, 1, 3, 1, 1, 1, 4, 4, 2, 2]
def baseStart_1864780 : Nat := 118140960795 + 1864780 * 2 ^ 59
def prefixEnd_1864780 : Nat := 4983230072969 + 3 ^ 40 * 1864780 * 2
def baseEnd_1864780 : Nat := 957528454891319273374039

theorem tailTrace_1864780 : CollatzResearch.WordTrace tailWord_1864780 prefixEnd_1864780 957528454891319273374039 := by
  unfold tailWord_1864780
  simp only [CollatzResearch.WordTrace]
  refine ⟨34007057092114006956847897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45342742789485342609130529 34007057092114006956847897)
  ·
    refine ⟨25505292819085505217635923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34007057092114006956847897 25505292819085505217635923)
    ·
      refine ⟨38257939228628257826453885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25505292819085505217635923 38257939228628257826453885)
      ·
        refine ⟨14346727210735596684920207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38257939228628257826453885 14346727210735596684920207)
        ·
          refine ⟨21520090816103395027380311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14346727210735596684920207 21520090816103395027380311)
          ·
            refine ⟨32280136224155092541070467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21520090816103395027380311 32280136224155092541070467)
            ·
              refine ⟨48420204336232638811605701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32280136224155092541070467 48420204336232638811605701)
              ·
                refine ⟨9078788313043619777176069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48420204336232638811605701 9078788313043619777176069)
                ·
                  refine ⟨1702272808695678708220513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9078788313043619777176069 1702272808695678708220513)
                  ·
                    refine ⟨1276704606521759031165385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1702272808695678708220513 1276704606521759031165385)
                    ·
                      refine ⟨957528454891319273374039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1276704606521759031165385 957528454891319273374039)
                      ·
                        rfl

theorem cell23_1864780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 4, 2, 2].length) (baseStart_1864780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1864780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1864780 prefixEnd_1864780 := by exact prefixLift 1864780
  have htrace : WordTrace (prefixWord ++ tailWord_1864780) baseStart_1864780 baseEnd_1864780 := by
    simpa [prefixWord, tailWord_1864780, baseEnd_1864780] using wordTrace_append hprefix tailTrace_1864780
  have hstable : (prefixWord ++ tailWord_1864780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864780).length < 2 ^ (prefixWord ++ tailWord_1864780).sum := by decide
  have hdescent : baseEnd_1864780 < baseStart_1864780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864816 : List Nat := [2, 1, 1, 1, 5, 1, 1, 1, 3, 7]
def baseStart_1864816 : Nat := 118140960795 + 1864816 * 2 ^ 59
def prefixEnd_1864816 : Nat := 4983230072969 + 3 ^ 40 * 1864816 * 2
def baseEnd_1864816 : Nat := 319182313398293710841291

theorem tailTrace_1864816 : CollatzResearch.WordTrace tailWord_1864816 prefixEnd_1864816 319182313398293710841291 := by
  unfold tailWord_1864816
  simp only [CollatzResearch.WordTrace]
  refine ⟨34007713606048796031003151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45343618141398394708004201 34007713606048796031003151)
  ·
    refine ⟨51011570409073194046504727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34007713606048796031003151 51011570409073194046504727)
    ·
      refine ⟨76517355613609791069757091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51011570409073194046504727 76517355613609791069757091)
      ·
        refine ⟨114776033420414686604635637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76517355613609791069757091 114776033420414686604635637)
        ·
          refine ⟨10760253133163876869184591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 114776033420414686604635637 10760253133163876869184591)
          ·
            refine ⟨16140379699745815303776887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10760253133163876869184591 16140379699745815303776887)
            ·
              refine ⟨24210569549618722955665331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16140379699745815303776887 24210569549618722955665331)
              ·
                refine ⟨36315854324428084433497997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24210569549618722955665331 36315854324428084433497997)
                ·
                  refine ⟨13618445371660531662561749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36315854324428084433497997 13618445371660531662561749)
                  ·
                    refine ⟨319182313398293710841291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13618445371660531662561749 319182313398293710841291)
                    ·
                      rfl

theorem cell23_1864816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 3, 7].length) (baseStart_1864816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1864816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1864816 prefixEnd_1864816 := by exact prefixLift 1864816
  have htrace : WordTrace (prefixWord ++ tailWord_1864816) baseStart_1864816 baseEnd_1864816 := by
    simpa [prefixWord, tailWord_1864816, baseEnd_1864816] using wordTrace_append hprefix tailTrace_1864816
  have hstable : (prefixWord ++ tailWord_1864816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864816).length < 2 ^ (prefixWord ++ tailWord_1864816).sum := by decide
  have hdescent : baseEnd_1864816 < baseStart_1864816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864833 : List Nat := [1, 2, 4, 2, 2, 1, 2, 1, 1, 7]
def baseStart_1864833 : Nat := 118140960795 + 1864833 * 2 ^ 59
def prefixEnd_1864833 : Nat := 4983230072969 + 3 ^ 40 * 1864833 * 2
def baseEnd_1864833 : Nat := 319185223122002522003765

theorem tailTrace_1864833 : CollatzResearch.WordTrace tailWord_1864833 prefixEnd_1864833 319185223122002522003765 := by
  unfold tailWord_1864833
  simp only [CollatzResearch.WordTrace]
  refine ⟨68016047253036003965375153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45344031502024002643583435 68016047253036003965375153)
  ·
    refine ⟨51012035439777002974031365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68016047253036003965375153 51012035439777002974031365)
    ·
      refine ⟨9564756644958188057630881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51012035439777002974031365 9564756644958188057630881)
      ·
        refine ⟨7173567483718641043223161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9564756644958188057630881 7173567483718641043223161)
        ·
          refine ⟨5380175612788980782417371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7173567483718641043223161 5380175612788980782417371)
          ·
            refine ⟨8070263419183471173626057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5380175612788980782417371 8070263419183471173626057)
            ·
              refine ⟨6052697564387603380219543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8070263419183471173626057 6052697564387603380219543)
              ·
                refine ⟨9079046346581405070329315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6052697564387603380219543 9079046346581405070329315)
                ·
                  refine ⟨13618569519872107605493973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9079046346581405070329315 13618569519872107605493973)
                  ·
                    refine ⟨319185223122002522003765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13618569519872107605493973 319185223122002522003765)
                    ·
                      rfl

theorem cell23_1864833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_1864833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1864833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1864833 prefixEnd_1864833 := by exact prefixLift 1864833
  have htrace : WordTrace (prefixWord ++ tailWord_1864833) baseStart_1864833 baseEnd_1864833 := by
    simpa [prefixWord, tailWord_1864833, baseEnd_1864833] using wordTrace_append hprefix tailTrace_1864833
  have hstable : (prefixWord ++ tailWord_1864833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864833).length < 2 ^ (prefixWord ++ tailWord_1864833).sum := by decide
  have hdescent : baseEnd_1864833 < baseStart_1864833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864837 : List Nat := [1, 3, 1, 1, 6, 2, 1, 3, 5]
def baseStart_1864837 : Nat := 118140960795 + 1864837 * 2 ^ 59
def prefixEnd_1864837 : Nat := 4983230072969 + 3 ^ 40 * 1864837 * 2
def baseEnd_1864837 : Nat := 106395302587625061151253

theorem tailTrace_1864837 : CollatzResearch.WordTrace tailWord_1864837 prefixEnd_1864837 106395302587625061151253 := by
  unfold tailWord_1864837
  simp only [CollatzResearch.WordTrace]
  refine ⟨68016193145021512648520765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45344128763347675099013843 68016193145021512648520765)
  ·
    refine ⟨25506072429383067243195287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68016193145021512648520765 25506072429383067243195287)
    ·
      refine ⟨38259108644074600864792931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25506072429383067243195287 38259108644074600864792931)
      ·
        refine ⟨57388662966111901297189397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38259108644074600864792931 57388662966111901297189397)
        ·
          refine ⟨2690093576536495373305753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 57388662966111901297189397 2690093576536495373305753)
          ·
            refine ⟨2017570182402371529979315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2690093576536495373305753 2017570182402371529979315)
            ·
              refine ⟨3026355273603557294968973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2017570182402371529979315 3026355273603557294968973)
              ·
                refine ⟨1134883227601333985613365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3026355273603557294968973 1134883227601333985613365)
                ·
                  refine ⟨106395302587625061151253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1134883227601333985613365 106395302587625061151253)
                  ·
                    rfl

theorem cell23_1864837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 3, 5].length) (baseStart_1864837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1864837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1864837 prefixEnd_1864837 := by exact prefixLift 1864837
  have htrace : WordTrace (prefixWord ++ tailWord_1864837) baseStart_1864837 baseEnd_1864837 := by
    simpa [prefixWord, tailWord_1864837, baseEnd_1864837] using wordTrace_append hprefix tailTrace_1864837
  have hstable : (prefixWord ++ tailWord_1864837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864837).length < 2 ^ (prefixWord ++ tailWord_1864837).sum := by decide
  have hdescent : baseEnd_1864837 < baseStart_1864837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864850 : List Nat := [3, 2, 3, 1, 1, 3, 1, 2, 2, 5]
def baseStart_1864850 : Nat := 118140960795 + 1864850 * 2 ^ 59
def prefixEnd_1864850 : Nat := 4983230072969 + 3 ^ 40 * 1864850 * 2
def baseEnd_1864850 : Nat := 319188132845711333166239

theorem tailTrace_1864850 : CollatzResearch.WordTrace tailWord_1864850 prefixEnd_1864850 319188132845711333166239 := by
  unfold tailWord_1864850
  simp only [CollatzResearch.WordTrace]
  refine ⟨17004166823493603967186001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45344444862649610579162669 17004166823493603967186001)
  ·
    refine ⟨12753125117620202975389501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17004166823493603967186001 12753125117620202975389501)
    ·
      refine ⟨4782421919107576115771063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12753125117620202975389501 4782421919107576115771063)
      ·
        refine ⟨7173632878661364173656595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4782421919107576115771063 7173632878661364173656595)
        ·
          refine ⟨10760449317992046260484893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7173632878661364173656595 10760449317992046260484893)
          ·
            refine ⟨4035168494247017347681835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10760449317992046260484893 4035168494247017347681835)
            ·
              refine ⟨6052752741370526021522753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4035168494247017347681835 6052752741370526021522753)
              ·
                refine ⟨4539564556027894516142065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6052752741370526021522753 4539564556027894516142065)
                ·
                  refine ⟨3404673417020920887106549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4539564556027894516142065 3404673417020920887106549)
                  ·
                    refine ⟨319188132845711333166239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3404673417020920887106549 319188132845711333166239)
                    ·
                      rfl

theorem cell23_1864850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_1864850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1864850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1864850 prefixEnd_1864850 := by exact prefixLift 1864850
  have htrace : WordTrace (prefixWord ++ tailWord_1864850) baseStart_1864850 baseEnd_1864850 := by
    simpa [prefixWord, tailWord_1864850, baseEnd_1864850] using wordTrace_append hprefix tailTrace_1864850
  have hstable : (prefixWord ++ tailWord_1864850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864850).length < 2 ^ (prefixWord ++ tailWord_1864850).sum := by decide
  have hdescent : baseEnd_1864850 < baseStart_1864850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864876 : List Nat := [2, 2, 1, 1, 1, 1, 1, 4, 10]
def baseStart_1864876 : Nat := 118140960795 + 1864876 * 2 ^ 59
def prefixEnd_1864876 : Nat := 4983230072969 + 3 ^ 40 * 1864876 * 2
def baseEnd_1864876 : Nat := 106397527670461210863733

theorem tailTrace_1864876 : CollatzResearch.WordTrace tailWord_1864876 prefixEnd_1864876 106397527670461210863733 := by
  unfold tailWord_1864876
  simp only [CollatzResearch.WordTrace]
  refine ⟨34008807795940111154595241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45345077061253481539460321 34008807795940111154595241)
  ·
    refine ⟨25506605846955083365946431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34008807795940111154595241 25506605846955083365946431)
    ·
      refine ⟨38259908770432625048919647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25506605846955083365946431 38259908770432625048919647)
      ·
        refine ⟨57389863155648937573379471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38259908770432625048919647 57389863155648937573379471)
        ·
          refine ⟨86084794733473406360069207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57389863155648937573379471 86084794733473406360069207)
          ·
            refine ⟨129127192100210109540103811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86084794733473406360069207 129127192100210109540103811)
            ·
              refine ⟨193690788150315164310155717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129127192100210109540103811 193690788150315164310155717)
              ·
                refine ⟨36317022778184093308154197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 193690788150315164310155717 36317022778184093308154197)
                ·
                  refine ⟨106397527670461210863733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 36317022778184093308154197 106397527670461210863733)
                  ·
                    rfl

theorem cell23_1864876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 10].length) (baseStart_1864876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1864876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1864876 prefixEnd_1864876 := by exact prefixLift 1864876
  have htrace : WordTrace (prefixWord ++ tailWord_1864876) baseStart_1864876 baseEnd_1864876 := by
    simpa [prefixWord, tailWord_1864876, baseEnd_1864876] using wordTrace_append hprefix tailTrace_1864876
  have hstable : (prefixWord ++ tailWord_1864876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864876).length < 2 ^ (prefixWord ++ tailWord_1864876).sum := by decide
  have hdescent : baseEnd_1864876 < baseStart_1864876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864947 : List Nat := [1, 1, 1, 2, 2, 5, 3, 1, 2, 3, 2]
def baseStart_1864947 : Nat := 118140960795 + 1864947 * 2 ^ 59
def prefixEnd_1864947 : Nat := 4983230072969 + 3 ^ 40 * 1864947 * 2
def baseEnd_1864947 : Nat := 957614206160620119985771

theorem tailTrace_1864947 : CollatzResearch.WordTrace tailWord_1864947 prefixEnd_1864947 957614206160620119985771 := by
  unfold tailWord_1864947
  simp only [CollatzResearch.WordTrace]
  refine ⟨68020205174623001435025095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45346803449748667623350063 68020205174623001435025095)
  ·
    refine ⟨102030307761934502152537643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68020205174623001435025095 102030307761934502152537643)
    ·
      refine ⟨153045461642901753228806465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102030307761934502152537643 153045461642901753228806465)
      ·
        refine ⟨114784096232176314921604849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153045461642901753228806465 114784096232176314921604849)
        ·
          refine ⟨86088072174132236191203637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114784096232176314921604849 86088072174132236191203637)
          ·
            refine ⟨8070756766324897142925341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86088072174132236191203637 8070756766324897142925341)
            ·
              refine ⟨3026533787371836428597003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8070756766324897142925341 3026533787371836428597003)
              ·
                refine ⟨4539800681057754642895505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3026533787371836428597003 4539800681057754642895505)
                ·
                  refine ⟨3404850510793315982171629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4539800681057754642895505 3404850510793315982171629)
                  ·
                    refine ⟨1276818941547493493314361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3404850510793315982171629 1276818941547493493314361)
                    ·
                      refine ⟨957614206160620119985771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1276818941547493493314361 957614206160620119985771)
                      ·
                        rfl

theorem cell23_1864947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 1, 2, 3, 2].length) (baseStart_1864947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1864947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1864947 prefixEnd_1864947 := by exact prefixLift 1864947
  have htrace : WordTrace (prefixWord ++ tailWord_1864947) baseStart_1864947 baseEnd_1864947 := by
    simpa [prefixWord, tailWord_1864947, baseEnd_1864947] using wordTrace_append hprefix tailTrace_1864947
  have hstable : (prefixWord ++ tailWord_1864947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864947).length < 2 ^ (prefixWord ++ tailWord_1864947).sum := by decide
  have hdescent : baseEnd_1864947 < baseStart_1864947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864953 : List Nat := [1, 2, 1, 3, 1, 1, 3, 4, 1, 6]
def baseStart_1864953 : Nat := 118140960795 + 1864953 * 2 ^ 59
def prefixEnd_1864953 : Nat := 4983230072969 + 3 ^ 40 * 1864953 * 2
def baseEnd_1864953 : Nat := 319205762348182365503581

theorem tailTrace_1864953 : CollatzResearch.WordTrace tailWord_1864953 prefixEnd_1864953 319205762348182365503581 := by
  unfold tailWord_1864953
  simp only [CollatzResearch.WordTrace]
  refine ⟨68020424012601264459743513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45346949341734176306495675 68020424012601264459743513)
  ·
    refine ⟨51015318009450948344807635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68020424012601264459743513 51015318009450948344807635)
    ·
      refine ⟨76522977014176422517211453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51015318009450948344807635 76522977014176422517211453)
      ·
        refine ⟨28696116380316158443954295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76522977014176422517211453 28696116380316158443954295)
        ·
          refine ⟨43044174570474237665931443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28696116380316158443954295 43044174570474237665931443)
          ·
            refine ⟨64566261855711356498897165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43044174570474237665931443 64566261855711356498897165)
            ·
              refine ⟨24212348195891758687086437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64566261855711356498897165 24212348195891758687086437)
              ·
                refine ⟨4539815286729704753828707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24212348195891758687086437 4539815286729704753828707)
                ·
                  refine ⟨6809722930094557130743061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4539815286729704753828707 6809722930094557130743061)
                  ·
                    refine ⟨319205762348182365503581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6809722930094557130743061 319205762348182365503581)
                    ·
                      rfl

theorem cell23_1864953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4, 1, 6].length) (baseStart_1864953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1864953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1864953 prefixEnd_1864953 := by exact prefixLift 1864953
  have htrace : WordTrace (prefixWord ++ tailWord_1864953) baseStart_1864953 baseEnd_1864953 := by
    simpa [prefixWord, tailWord_1864953, baseEnd_1864953] using wordTrace_append hprefix tailTrace_1864953
  have hstable : (prefixWord ++ tailWord_1864953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864953).length < 2 ^ (prefixWord ++ tailWord_1864953).sum := by decide
  have hdescent : baseEnd_1864953 < baseStart_1864953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864954 : List Nat := [3, 1, 1, 1, 1, 4, 4, 3, 1, 1, 3]
def baseStart_1864954 : Nat := 118140960795 + 1864954 * 2 ^ 59
def prefixEnd_1864954 : Nat := 4983230072969 + 3 ^ 40 * 1864954 * 2
def baseEnd_1864954 : Nat := 957617800525201592598239

theorem tailTrace_1864954 : CollatzResearch.WordTrace tailWord_1864954 prefixEnd_1864954 957617800525201592598239 := by
  unfold tailWord_1864954
  simp only [CollatzResearch.WordTrace]
  refine ⟨17005115121399410407632479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45346973657065094420353277 17005115121399410407632479)
  ·
    refine ⟨25507672682099115611448719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17005115121399410407632479 25507672682099115611448719)
    ·
      refine ⟨38261509023148673417173079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25507672682099115611448719 38261509023148673417173079)
      ·
        refine ⟨57392263534723010125759619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38261509023148673417173079 57392263534723010125759619)
        ·
          refine ⟨86088395302084515188639429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57392263534723010125759619 86088395302084515188639429)
          ·
            refine ⟨16141574119140846597869893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86088395302084515188639429 16141574119140846597869893)
            ·
              refine ⟨3026545147338908737100605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16141574119140846597869893 3026545147338908737100605)
              ·
                refine ⟨1134954430252090776412727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3026545147338908737100605 1134954430252090776412727)
                ·
                  refine ⟨1702431645378136164619091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1134954430252090776412727 1702431645378136164619091)
                  ·
                    refine ⟨2553647468067204246928637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1702431645378136164619091 2553647468067204246928637)
                    ·
                      refine ⟨957617800525201592598239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2553647468067204246928637 957617800525201592598239)
                      ·
                        rfl

theorem cell23_1864954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 3, 1, 1, 3].length) (baseStart_1864954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1864954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1864954 prefixEnd_1864954 := by exact prefixLift 1864954
  have htrace : WordTrace (prefixWord ++ tailWord_1864954) baseStart_1864954 baseEnd_1864954 := by
    simpa [prefixWord, tailWord_1864954, baseEnd_1864954] using wordTrace_append hprefix tailTrace_1864954
  have hstable : (prefixWord ++ tailWord_1864954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864954).length < 2 ^ (prefixWord ++ tailWord_1864954).sum := by decide
  have hdescent : baseEnd_1864954 < baseStart_1864954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864983 : List Nat := [1, 1, 3, 4, 1, 1, 2, 10]
def baseStart_1864983 : Nat := 118140960795 + 1864983 * 2 ^ 59
def prefixEnd_1864983 : Nat := 4983230072969 + 3 ^ 40 * 1864983 * 2
def baseEnd_1864983 : Nat := 35467877461636369597615

theorem tailTrace_1864983 : CollatzResearch.WordTrace tailWord_1864983 prefixEnd_1864983 35467877461636369597615 := by
  unfold tailWord_1864983
  simp only [CollatzResearch.WordTrace]
  refine ⟨68021518202492579583335603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45347678801661719722223735 68021518202492579583335603)
  ·
    refine ⟨102032277303738869375003405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68021518202492579583335603 102032277303738869375003405)
    ·
      refine ⟨38262103988902076015626277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102032277303738869375003405 38262103988902076015626277)
      ·
        refine ⟨7174144497919139252929927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38262103988902076015626277 7174144497919139252929927)
        ·
          refine ⟨10761216746878708879394891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7174144497919139252929927 10761216746878708879394891)
          ·
            refine ⟨16141825120318063319092337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10761216746878708879394891 16141825120318063319092337)
            ·
              refine ⟨12106368840238547489319253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16141825120318063319092337 12106368840238547489319253)
              ·
                refine ⟨35467877461636369597615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 12106368840238547489319253 35467877461636369597615)
                ·
                  rfl

theorem cell23_1864983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 10].length) (baseStart_1864983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1864983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1864983 prefixEnd_1864983 := by exact prefixLift 1864983
  have htrace : WordTrace (prefixWord ++ tailWord_1864983) baseStart_1864983 baseEnd_1864983 := by
    simpa [prefixWord, tailWord_1864983, baseEnd_1864983] using wordTrace_append hprefix tailTrace_1864983
  have hstable : (prefixWord ++ tailWord_1864983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864983).length < 2 ^ (prefixWord ++ tailWord_1864983).sum := by decide
  have hdescent : baseEnd_1864983 < baseStart_1864983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864994 : List Nat := [3, 3, 1, 1, 4, 1, 2, 2, 1, 1, 4]
def baseStart_1864994 : Nat := 118140960795 + 1864994 * 2 ^ 59
def prefixEnd_1864994 : Nat := 4983230072969 + 3 ^ 40 * 1864994 * 2
def baseEnd_1864994 : Nat := 957638339751381436098055

theorem tailTrace_1864994 : CollatzResearch.WordTrace tailWord_1864994 prefixEnd_1864994 957638339751381436098055 := by
  unfold tailWord_1864994
  simp only [CollatzResearch.WordTrace]
  refine ⟨17005479851363182115496509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45347946270301818974657357 17005479851363182115496509)
  ·
    refine ⟨6377054944261193293311191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17005479851363182115496509 6377054944261193293311191)
    ·
      refine ⟨9565582416391789939966787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6377054944261193293311191 9565582416391789939966787)
      ·
        refine ⟨14348373624587684909950181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9565582416391789939966787 14348373624587684909950181)
        ·
          refine ⟨2690320054610190920615659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14348373624587684909950181 2690320054610190920615659)
          ·
            refine ⟨4035480081915286380923489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2690320054610190920615659 4035480081915286380923489)
            ·
              refine ⟨3026610061436464785692617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4035480081915286380923489 3026610061436464785692617)
              ·
                refine ⟨2269957546077348589269463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3026610061436464785692617 2269957546077348589269463)
                ·
                  refine ⟨3404936319116022883904195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2269957546077348589269463 3404936319116022883904195)
                  ·
                    refine ⟨5107404478674034325856293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3404936319116022883904195 5107404478674034325856293)
                    ·
                      refine ⟨957638339751381436098055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5107404478674034325856293 957638339751381436098055)
                      ·
                        rfl

theorem cell23_1864994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 2, 1, 1, 4].length) (baseStart_1864994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1864994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1864994 prefixEnd_1864994 := by exact prefixLift 1864994
  have htrace : WordTrace (prefixWord ++ tailWord_1864994) baseStart_1864994 baseEnd_1864994 := by
    simpa [prefixWord, tailWord_1864994, baseEnd_1864994] using wordTrace_append hprefix tailTrace_1864994
  have hstable : (prefixWord ++ tailWord_1864994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864994).length < 2 ^ (prefixWord ++ tailWord_1864994).sum := by decide
  have hdescent : baseEnd_1864994 < baseStart_1864994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864997 : List Nat := [1, 3, 1, 2, 4, 1, 1, 4, 1, 2, 3]
def baseStart_1864997 : Nat := 118140960795 + 1864997 * 2 ^ 59
def prefixEnd_1864997 : Nat := 4983230072969 + 3 ^ 40 * 1864997 * 2
def baseEnd_1864997 : Nat := 957639880193344924360541

theorem tailTrace_1864997 : CollatzResearch.WordTrace tailWord_1864997 prefixEnd_1864997 957639880193344924360541 := by
  unfold tailWord_1864997
  simp only [CollatzResearch.WordTrace]
  refine ⟨68022028824441859974345245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45348019216294573316230163 68022028824441859974345245)
  ·
    refine ⟨25508260809165697490379467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68022028824441859974345245 25508260809165697490379467)
    ·
      refine ⟨38262391213748546235569201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25508260809165697490379467 38262391213748546235569201)
      ·
        refine ⟨28696793410311409676676901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38262391213748546235569201 28696793410311409676676901)
        ·
          refine ⟨5380648764433389314376919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28696793410311409676676901 5380648764433389314376919)
          ·
            refine ⟨8070973146650083971565379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5380648764433389314376919 8070973146650083971565379)
            ·
              refine ⟨12106459719975125957348069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8070973146650083971565379 12106459719975125957348069)
              ·
                refine ⟨2269961197495336117002763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12106459719975125957348069 2269961197495336117002763)
                ·
                  refine ⟨3404941796243004175504145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2269961197495336117002763 3404941796243004175504145)
                  ·
                    refine ⟨2553706347182253131628109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3404941796243004175504145 2553706347182253131628109)
                    ·
                      refine ⟨957639880193344924360541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2553706347182253131628109 957639880193344924360541)
                      ·
                        rfl

theorem cell23_1864997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 4, 1, 2, 3].length) (baseStart_1864997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1864997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1864997 prefixEnd_1864997 := by exact prefixLift 1864997
  have htrace : WordTrace (prefixWord ++ tailWord_1864997) baseStart_1864997 baseEnd_1864997 := by
    simpa [prefixWord, tailWord_1864997, baseEnd_1864997] using wordTrace_append hprefix tailTrace_1864997
  have hstable : (prefixWord ++ tailWord_1864997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864997).length < 2 ^ (prefixWord ++ tailWord_1864997).sum := by decide
  have hdescent : baseEnd_1864997 < baseStart_1864997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865000 : List Nat := [2, 1, 5, 1, 2, 2, 1, 9]
def baseStart_1865000 : Nat := 118140960795 + 1865000 * 2 ^ 59
def prefixEnd_1865000 : Nat := 4983230072969 + 3 ^ 40 * 1865000 * 2
def baseEnd_1865000 : Nat := 35468200764270681949001

theorem tailTrace_1865000 : CollatzResearch.WordTrace tailWord_1865000 prefixEnd_1865000 35468200764270681949001 := by
  unfold tailWord_1865000
  simp only [CollatzResearch.WordTrace]
  refine ⟨34011069121715495743352227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45348092162287327657802969 34011069121715495743352227)
  ·
    refine ⟨51016603682573243615028341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34011069121715495743352227 51016603682573243615028341)
    ·
      refine ⟨4782806595241241588908907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51016603682573243615028341 4782806595241241588908907)
      ·
        refine ⟨7174209892861862383363361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4782806595241241588908907 7174209892861862383363361)
        ·
          refine ⟨5380657419646396787522521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7174209892861862383363361 5380657419646396787522521)
          ·
            refine ⟨4035493064734797590641891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5380657419646396787522521 4035493064734797590641891)
            ·
              refine ⟨6053239597102196385962837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4035493064734797590641891 6053239597102196385962837)
              ·
                refine ⟨35468200764270681949001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6053239597102196385962837 35468200764270681949001)
                ·
                  rfl

theorem cell23_1865000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 9].length) (baseStart_1865000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1865000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1865000 prefixEnd_1865000 := by exact prefixLift 1865000
  have htrace : WordTrace (prefixWord ++ tailWord_1865000) baseStart_1865000 baseEnd_1865000 := by
    simpa [prefixWord, tailWord_1865000, baseEnd_1865000] using wordTrace_append hprefix tailTrace_1865000
  have hstable : (prefixWord ++ tailWord_1865000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865000).length < 2 ^ (prefixWord ++ tailWord_1865000).sum := by decide
  have hdescent : baseEnd_1865000 < baseStart_1865000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865011 : List Nat := [1, 1, 1, 2, 5, 2, 3, 3, 1, 2, 2]
def baseStart_1865011 : Nat := 118140960795 + 1865011 * 2 ^ 59
def prefixEnd_1865011 : Nat := 4983230072969 + 3 ^ 40 * 1865011 * 2
def baseEnd_1865011 : Nat := 957647068922507869585477

theorem tailTrace_1865011 : CollatzResearch.WordTrace tailWord_1865011 prefixEnd_1865011 957647068922507869585477 := by
  unfold tailWord_1865011
  simp only [CollatzResearch.WordTrace]
  refine ⟨68022539446391140365354887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45348359630927426910236591 68022539446391140365354887)
  ·
    refine ⟨102033809169586710548032331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68022539446391140365354887 102033809169586710548032331)
    ·
      refine ⟨153050713754380065822048497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102033809169586710548032331 153050713754380065822048497)
      ·
        refine ⟨114788035315785049366536373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153050713754380065822048497 114788035315785049366536373)
        ·
          refine ⟨10761378310854848378112785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 114788035315785049366536373 10761378310854848378112785)
          ·
            refine ⟨8071033733141136283584589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10761378310854848378112785 8071033733141136283584589)
            ·
              refine ⟨3026637649927926106344221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8071033733141136283584589 3026637649927926106344221)
              ·
                refine ⟨1134989118722972289879083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3026637649927926106344221 1134989118722972289879083)
                ·
                  refine ⟨1702483678084458434818625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1134989118722972289879083 1702483678084458434818625)
                  ·
                    refine ⟨1276862758563343826113969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1702483678084458434818625 1276862758563343826113969)
                    ·
                      refine ⟨957647068922507869585477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1276862758563343826113969 957647068922507869585477)
                      ·
                        rfl

theorem cell23_1865011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 3, 1, 2, 2].length) (baseStart_1865011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1865011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1865011 prefixEnd_1865011 := by exact prefixLift 1865011
  have htrace : WordTrace (prefixWord ++ tailWord_1865011) baseStart_1865011 baseEnd_1865011 := by
    simpa [prefixWord, tailWord_1865011, baseEnd_1865011] using wordTrace_append hprefix tailTrace_1865011
  have hstable : (prefixWord ++ tailWord_1865011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865011).length < 2 ^ (prefixWord ++ tailWord_1865011).sum := by decide
  have hdescent : baseEnd_1865011 < baseStart_1865011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865017 : List Nat := [1, 2, 1, 6, 3, 1, 9]
def baseStart_1865017 : Nat := 118140960795 + 1865017 * 2 ^ 59
def prefixEnd_1865017 : Nat := 4983230072969 + 3 ^ 40 * 1865017 * 2
def baseEnd_1865017 : Nat := 11822841355634998100129

theorem tailTrace_1865017 : CollatzResearch.WordTrace tailWord_1865017 prefixEnd_1865017 11822841355634998100129 := by
  unfold tailWord_1865017
  simp only [CollatzResearch.WordTrace]
  refine ⟨68022758284369403390073305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45348505522912935593382203 68022758284369403390073305)
  ·
    refine ⟨51017068713277052542554979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68022758284369403390073305 51017068713277052542554979)
    ·
      refine ⟨76525603069915578813832469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51017068713277052542554979 76525603069915578813832469)
      ·
        refine ⟨3587137643902292756898397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 76525603069915578813832469 3587137643902292756898397)
        ·
          refine ⟨1345176616463359783836899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3587137643902292756898397 1345176616463359783836899)
          ·
            refine ⟨2017764924695039675755349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1345176616463359783836899 2017764924695039675755349)
            ·
              refine ⟨11822841355634998100129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2017764924695039675755349 11822841355634998100129)
              ·
                rfl

theorem cell23_1865017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 9].length) (baseStart_1865017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1865017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1865017 prefixEnd_1865017 := by exact prefixLift 1865017
  have htrace : WordTrace (prefixWord ++ tailWord_1865017) baseStart_1865017 baseEnd_1865017 := by
    simpa [prefixWord, tailWord_1865017, baseEnd_1865017] using wordTrace_append hprefix tailTrace_1865017
  have hstable : (prefixWord ++ tailWord_1865017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865017).length < 2 ^ (prefixWord ++ tailWord_1865017).sum := by decide
  have hdescent : baseEnd_1865017 < baseStart_1865017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865027 : List Nat := [1, 1, 1, 3, 1, 3, 1, 6, 2, 1, 3]
def baseStart_1865027 : Nat := 118140960795 + 1865027 * 2 ^ 59
def prefixEnd_1865027 : Nat := 4983230072969 + 3 ^ 40 * 1865027 * 2
def baseEnd_1865027 : Nat := 957655284612979806985403

theorem tailTrace_1865027 : CollatzResearch.WordTrace tailWord_1865027 prefixEnd_1865027 957655284612979806985403 := by
  unfold tailWord_1865027
  simp only [CollatzResearch.WordTrace]
  refine ⟨68023123014333175097937335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45348748676222116731958223 68023123014333175097937335)
  ·
    refine ⟨102034684521499762646906003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68023123014333175097937335 102034684521499762646906003)
    ·
      refine ⟨153052026782249643970359005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102034684521499762646906003 153052026782249643970359005)
      ·
        refine ⟨57394510043343616488884627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153052026782249643970359005 57394510043343616488884627)
        ·
          refine ⟨86091765065015424733326941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57394510043343616488884627 86091765065015424733326941)
          ·
            refine ⟨32284411899380784274997603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86091765065015424733326941 32284411899380784274997603)
            ·
              refine ⟨48426617849071176412496405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32284411899380784274997603 48426617849071176412496405)
              ·
                refine ⟨2269997711675211394335769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48426617849071176412496405 2269997711675211394335769)
                ·
                  refine ⟨1702498283756408545751827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2269997711675211394335769 1702498283756408545751827)
                  ·
                    refine ⟨2553747425634612818627741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1702498283756408545751827 2553747425634612818627741)
                    ·
                      refine ⟨957655284612979806985403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2553747425634612818627741 957655284612979806985403)
                      ·
                        rfl

theorem cell23_1865027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 6, 2, 1, 3].length) (baseStart_1865027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1865027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1865027 prefixEnd_1865027 := by exact prefixLift 1865027
  have htrace : WordTrace (prefixWord ++ tailWord_1865027) baseStart_1865027 baseEnd_1865027 := by
    simpa [prefixWord, tailWord_1865027, baseEnd_1865027] using wordTrace_append hprefix tailTrace_1865027
  have hstable : (prefixWord ++ tailWord_1865027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865027).length < 2 ^ (prefixWord ++ tailWord_1865027).sum := by decide
  have hdescent : baseEnd_1865027 < baseStart_1865027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865028 : List Nat := [2, 3, 4, 1, 1, 3, 1, 1, 3, 2, 2]
def baseStart_1865028 : Nat := 118140960795 + 1865028 * 2 ^ 59
def prefixEnd_1865028 : Nat := 4983230072969 + 3 ^ 40 * 1865028 * 2
def baseEnd_1865028 : Nat := 957655798093634303072899

theorem tailTrace_1865028 : CollatzResearch.WordTrace tailWord_1865028 prefixEnd_1865028 957655798093634303072899 := by
  unfold tailWord_1865028
  simp only [CollatzResearch.WordTrace]
  refine ⟨34011579743664776134361869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45348772991553034845815825 34011579743664776134361869)
  ·
    refine ⟨12754342403874291050385701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34011579743664776134361869 12754342403874291050385701)
    ·
      refine ⟨2391439200726429571947319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12754342403874291050385701 2391439200726429571947319)
      ·
        refine ⟨3587158801089644357920979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2391439200726429571947319 3587158801089644357920979)
        ·
          refine ⟨5380738201634466536881469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3587158801089644357920979 5380738201634466536881469)
          ·
            refine ⟨2017776825612924951330551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5380738201634466536881469 2017776825612924951330551)
            ·
              refine ⟨3026665238419387426995827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2017776825612924951330551 3026665238419387426995827)
              ·
                refine ⟨4539997857629081140493741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3026665238419387426995827 4539997857629081140493741)
                ·
                  refine ⟨1702499196610905427685153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4539997857629081140493741 1702499196610905427685153)
                  ·
                    refine ⟨1276874397458179070763865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1702499196610905427685153 1276874397458179070763865)
                    ·
                      refine ⟨957655798093634303072899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1276874397458179070763865 957655798093634303072899)
                      ·
                        rfl

theorem cell23_1865028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_1865028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1865028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1865028 prefixEnd_1865028 := by exact prefixLift 1865028
  have htrace : WordTrace (prefixWord ++ tailWord_1865028) baseStart_1865028 baseEnd_1865028 := by
    simpa [prefixWord, tailWord_1865028, baseEnd_1865028] using wordTrace_append hprefix tailTrace_1865028
  have hstable : (prefixWord ++ tailWord_1865028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865028).length < 2 ^ (prefixWord ++ tailWord_1865028).sum := by decide
  have hdescent : baseEnd_1865028 < baseStart_1865028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865043 : List Nat := [1, 1, 1, 2, 1, 1, 6, 1, 1, 8]
def baseStart_1865043 : Nat := 118140960795 + 1865043 * 2 ^ 59
def prefixEnd_1865043 : Nat := 4983230072969 + 3 ^ 40 * 1865043 * 2
def baseEnd_1865043 : Nat := 319221166767817248128443

theorem tailTrace_1865043 : CollatzResearch.WordTrace tailWord_1865043 prefixEnd_1865043 319221166767817248128443 := by
  unfold tailWord_1865043
  simp only [CollatzResearch.WordTrace]
  refine ⟨68023706582275209830519783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45349137721516806553679855 68023706582275209830519783)
  ·
    refine ⟨102035559873412814745779675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68023706582275209830519783 102035559873412814745779675)
    ·
      refine ⟨153053339810119222118669513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102035559873412814745779675 153053339810119222118669513)
      ·
        refine ⟨114790004857589416589002135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153053339810119222118669513 114790004857589416589002135)
        ·
          refine ⟨172185007286384124883503203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114790004857589416589002135 172185007286384124883503203)
          ·
            refine ⟨258277510929576187325254805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172185007286384124883503203 258277510929576187325254805)
            ·
              refine ⟨12106758324823883780871319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 258277510929576187325254805 12106758324823883780871319)
              ·
                refine ⟨18160137487235825671306979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12106758324823883780871319 18160137487235825671306979)
                ·
                  refine ⟨27240206230853738506960469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18160137487235825671306979 27240206230853738506960469)
                  ·
                    refine ⟨319221166767817248128443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 27240206230853738506960469 319221166767817248128443)
                    ·
                      rfl

theorem cell23_1865043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 8].length) (baseStart_1865043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1865043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1865043 prefixEnd_1865043 := by exact prefixLift 1865043
  have htrace : WordTrace (prefixWord ++ tailWord_1865043) baseStart_1865043 baseEnd_1865043 := by
    simpa [prefixWord, tailWord_1865043, baseEnd_1865043] using wordTrace_append hprefix tailTrace_1865043
  have hstable : (prefixWord ++ tailWord_1865043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865043).length < 2 ^ (prefixWord ++ tailWord_1865043).sum := by decide
  have hdescent : baseEnd_1865043 < baseStart_1865043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865044 : List Nat := [2, 4, 1, 1, 2, 1, 3, 3, 2, 1, 3]
def baseStart_1865044 : Nat := 118140960795 + 1865044 * 2 ^ 59
def prefixEnd_1865044 : Nat := 4983230072969 + 3 ^ 40 * 1865044 * 2
def baseEnd_1865044 : Nat := 957664013784106240472825

theorem tailTrace_1865044 : CollatzResearch.WordTrace tailWord_1865044 prefixEnd_1865044 957664013784106240472825 := by
  unfold tailWord_1865044
  simp only [CollatzResearch.WordTrace]
  refine ⟨34011871527635793500653093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45349162036847724667537457 34011871527635793500653093)
  ·
    refine ⟨6377225911431711281372455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34011871527635793500653093 6377225911431711281372455)
    ·
      refine ⟨9565838867147566922058683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6377225911431711281372455 9565838867147566922058683)
      ·
        refine ⟨14348758300721350383088025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9565838867147566922058683 14348758300721350383088025)
        ·
          refine ⟨10761568725541012787316019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14348758300721350383088025 10761568725541012787316019)
          ·
            refine ⟨16142353088311519180974029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10761568725541012787316019 16142353088311519180974029)
            ·
              refine ⟨6053382408116819692865261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16142353088311519180974029 6053382408116819692865261)
              ·
                refine ⟨2270018403043807384824473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6053382408116819692865261 2270018403043807384824473)
                ·
                  refine ⟨1702513802282855538618355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2270018403043807384824473 1702513802282855538618355)
                  ·
                    refine ⟨2553770703424283307927533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1702513802282855538618355 2553770703424283307927533)
                    ·
                      refine ⟨957664013784106240472825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2553770703424283307927533 957664013784106240472825)
                      ·
                        rfl

theorem cell23_1865044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 3, 2, 1, 3].length) (baseStart_1865044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1865044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1865044 prefixEnd_1865044 := by exact prefixLift 1865044
  have htrace : WordTrace (prefixWord ++ tailWord_1865044) baseStart_1865044 baseEnd_1865044 := by
    simpa [prefixWord, tailWord_1865044, baseEnd_1865044] using wordTrace_append hprefix tailTrace_1865044
  have hstable : (prefixWord ++ tailWord_1865044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865044).length < 2 ^ (prefixWord ++ tailWord_1865044).sum := by decide
  have hdescent : baseEnd_1865044 < baseStart_1865044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865097 : List Nat := [1, 2, 1, 1, 7, 1, 1, 1, 2, 2, 4]
def baseStart_1865097 : Nat := 118140960795 + 1865097 * 2 ^ 59
def prefixEnd_1865097 : Nat := 4983230072969 + 3 ^ 40 * 1865097 * 2
def baseEnd_1865097 : Nat := 957691228258794533110081

theorem tailTrace_1865097 : CollatzResearch.WordTrace tailWord_1865097 prefixEnd_1865097 957691228258794533110081 := by
  unfold tailWord_1865097
  simp only [CollatzResearch.WordTrace]
  refine ⟨68025676124079577052985545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45350450749386384701990363 68025676124079577052985545)
  ·
    refine ⟨51019257093059682789739159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68025676124079577052985545 51019257093059682789739159)
    ·
      refine ⟨76528885639589524184608739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51019257093059682789739159 76528885639589524184608739)
      ·
        refine ⟨114793328459384286276913109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76528885639589524184608739 114793328459384286276913109)
        ·
          refine ⟨2690468635766819209615151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 114793328459384286276913109 2690468635766819209615151)
          ·
            refine ⟨4035702953650228814422727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2690468635766819209615151 4035702953650228814422727)
            ·
              refine ⟨6053554430475343221634091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4035702953650228814422727 6053554430475343221634091)
              ·
                refine ⟨9080331645713014832451137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6053554430475343221634091 9080331645713014832451137)
                ·
                  refine ⟨6810248734284761124338353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9080331645713014832451137 6810248734284761124338353)
                  ·
                    refine ⟨5107686550713570843253765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6810248734284761124338353 5107686550713570843253765)
                    ·
                      refine ⟨957691228258794533110081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5107686550713570843253765 957691228258794533110081)
                      ·
                        rfl

theorem cell23_1865097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 2, 2, 4].length) (baseStart_1865097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1865097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1865097 prefixEnd_1865097 := by exact prefixLift 1865097
  have htrace : WordTrace (prefixWord ++ tailWord_1865097) baseStart_1865097 baseEnd_1865097 := by
    simpa [prefixWord, tailWord_1865097, baseEnd_1865097] using wordTrace_append hprefix tailTrace_1865097
  have hstable : (prefixWord ++ tailWord_1865097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865097).length < 2 ^ (prefixWord ++ tailWord_1865097).sum := by decide
  have hdescent : baseEnd_1865097 < baseStart_1865097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865120 : List Nat := [2, 1, 1, 4, 1, 2, 3, 1, 1, 7]
def baseStart_1865120 : Nat := 118140960795 + 1865120 * 2 ^ 59
def prefixEnd_1865120 : Nat := 4983230072969 + 3 ^ 40 * 1865120 * 2
def baseEnd_1865120 : Nat := 319234346104615981040825

theorem tailTrace_1865120 : CollatzResearch.WordTrace tailWord_1865120 prefixEnd_1865120 319234346104615981040825 := by
  unfold tailWord_1865120
  simp only [CollatzResearch.WordTrace]
  refine ⟨34013257501498125990536407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45351010001997501320715209 34013257501498125990536407)
  ·
    refine ⟨51019886252247188985804611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34013257501498125990536407 51019886252247188985804611)
    ·
      refine ⟨76529829378370783478706917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51019886252247188985804611 76529829378370783478706917)
      ·
        refine ⟨14349343008444521902257547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76529829378370783478706917 14349343008444521902257547)
        ·
          refine ⟨21524014512666782853386321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14349343008444521902257547 21524014512666782853386321)
          ·
            refine ⟨16143010884500087140039741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21524014512666782853386321 16143010884500087140039741)
            ·
              refine ⟨6053629081687532677514903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16143010884500087140039741 6053629081687532677514903)
              ·
                refine ⟨9080443622531299016272355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6053629081687532677514903 9080443622531299016272355)
                ·
                  refine ⟨13620665433796948524408533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9080443622531299016272355 13620665433796948524408533)
                  ·
                    refine ⟨319234346104615981040825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13620665433796948524408533 319234346104615981040825)
                    ·
                      rfl

theorem cell23_1865120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 1, 7].length) (baseStart_1865120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1865120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1865120 prefixEnd_1865120 := by exact prefixLift 1865120
  have htrace : WordTrace (prefixWord ++ tailWord_1865120) baseStart_1865120 baseEnd_1865120 := by
    simpa [prefixWord, tailWord_1865120, baseEnd_1865120] using wordTrace_append hprefix tailTrace_1865120
  have hstable : (prefixWord ++ tailWord_1865120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865120).length < 2 ^ (prefixWord ++ tailWord_1865120).sum := by decide
  have hdescent : baseEnd_1865120 < baseStart_1865120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865167 : List Nat := [1, 1, 2, 1, 1, 4, 4, 2, 3, 4]
def baseStart_1865167 : Nat := 118140960795 + 1865167 * 2 ^ 59
def prefixEnd_1865167 : Nat := 4983230072969 + 3 ^ 40 * 1865167 * 2
def baseEnd_1865167 : Nat := 319242390634869753078253

theorem tailTrace_1865167 : CollatzResearch.WordTrace tailWord_1865167 prefixEnd_1865167 319242390634869753078253 := by
  unfold tailWord_1865167
  simp only [CollatzResearch.WordTrace]
  refine ⟨68028229233825979008033755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45352152822550652672022503 68028229233825979008033755)
  ·
    refine ⟨102042343850738968512050633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68028229233825979008033755 102042343850738968512050633)
    ·
      refine ⟨76531757888054226384037975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102042343850738968512050633 76531757888054226384037975)
      ·
        refine ⟨114797636832081339576056963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76531757888054226384037975 114797636832081339576056963)
        ·
          refine ⟨172196455248122009364085445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114797636832081339576056963 172196455248122009364085445)
          ·
            refine ⟨32286835359022876755766021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172196455248122009364085445 32286835359022876755766021)
            ·
              refine ⟨6053781629816789391706129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32286835359022876755766021 6053781629816789391706129)
              ·
                refine ⟨4540336222362592043779597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6053781629816789391706129 4540336222362592043779597)
                ·
                  refine ⟨1702626083385972016417349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4540336222362592043779597 1702626083385972016417349)
                  ·
                    refine ⟨319242390634869753078253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1702626083385972016417349 319242390634869753078253)
                    ·
                      rfl

theorem cell23_1865167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 2, 3, 4].length) (baseStart_1865167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1865167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1865167 prefixEnd_1865167 := by exact prefixLift 1865167
  have htrace : WordTrace (prefixWord ++ tailWord_1865167) baseStart_1865167 baseEnd_1865167 := by
    simpa [prefixWord, tailWord_1865167, baseEnd_1865167] using wordTrace_append hprefix tailTrace_1865167
  have hstable : (prefixWord ++ tailWord_1865167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865167).length < 2 ^ (prefixWord ++ tailWord_1865167).sum := by decide
  have hdescent : baseEnd_1865167 < baseStart_1865167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865174 : List Nat := [5, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4]
def baseStart_1865174 : Nat := 118140960795 + 1865174 * 2 ^ 59
def prefixEnd_1865174 : Nat := 4983230072969 + 3 ^ 40 * 1865174 * 2
def baseEnd_1865174 : Nat := 957730766269190731847227

theorem tailTrace_1865174 : CollatzResearch.WordTrace tailWord_1865174 prefixEnd_1865174 957730766269190731847227 := by
  unfold tailWord_1865174
  simp only [CollatzResearch.WordTrace]
  refine ⟨4251780284050038700221161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45352323029867079469025717 4251780284050038700221161)
  ·
    refine ⟨3188835213037529025165871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4251780284050038700221161 3188835213037529025165871)
    ·
      refine ⟨4783252819556293537748807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3188835213037529025165871 4783252819556293537748807)
      ·
        refine ⟨7174879229334440306623211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4783252819556293537748807 7174879229334440306623211)
        ·
          refine ⟨10762318844001660459934817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7174879229334440306623211 10762318844001660459934817)
          ·
            refine ⟨8071739133001245344951113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10762318844001660459934817 8071739133001245344951113)
            ·
              refine ⟨6053804349750934008713335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8071739133001245344951113 6053804349750934008713335)
              ·
                refine ⟨9080706524626401013070003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6053804349750934008713335 9080706524626401013070003)
                ·
                  refine ⟨13621059786939601519605005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9080706524626401013070003 13621059786939601519605005)
                  ·
                    refine ⟨5107897420102350569851877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13621059786939601519605005 5107897420102350569851877)
                    ·
                      refine ⟨957730766269190731847227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5107897420102350569851877 957730766269190731847227)
                      ·
                        rfl

theorem cell23_1865174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_1865174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1865174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1865174 prefixEnd_1865174 := by exact prefixLift 1865174
  have htrace : WordTrace (prefixWord ++ tailWord_1865174) baseStart_1865174 baseEnd_1865174 := by
    simpa [prefixWord, tailWord_1865174, baseEnd_1865174] using wordTrace_append hprefix tailTrace_1865174
  have hstable : (prefixWord ++ tailWord_1865174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865174).length < 2 ^ (prefixWord ++ tailWord_1865174).sum := by decide
  have hdescent : baseEnd_1865174 < baseStart_1865174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865177 : List Nat := [1, 2, 1, 2, 4, 2, 2, 1, 1, 4, 3]
def baseStart_1865177 : Nat := 118140960795 + 1865177 * 2 ^ 59
def prefixEnd_1865177 : Nat := 4983230072969 + 3 ^ 40 * 1865177 * 2
def baseEnd_1865177 : Nat := 957732306711154220109713

theorem tailTrace_1865177 : CollatzResearch.WordTrace tailWord_1865177 prefixEnd_1865177 957732306711154220109713 := by
  unfold tailWord_1865177
  simp only [CollatzResearch.WordTrace]
  refine ⟨68028593963789750715897785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45352395975859833810598523 68028593963789750715897785)
  ·
    refine ⟨51021445472842313036923339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68028593963789750715897785 51021445472842313036923339)
    ·
      refine ⟨76532168209263469555385009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51021445472842313036923339 76532168209263469555385009)
      ·
        refine ⟨57399126156947602166538757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76532168209263469555385009 57399126156947602166538757)
        ·
          refine ⟨10762336154427675406226017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57399126156947602166538757 10762336154427675406226017)
          ·
            refine ⟨8071752115820756554669513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10762336154427675406226017 8071752115820756554669513)
            ·
              refine ⟨6053814086865567416002135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8071752115820756554669513 6053814086865567416002135)
              ·
                refine ⟨9080721130298351124003203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6053814086865567416002135 9080721130298351124003203)
                ·
                  refine ⟨13621081695447526686004805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9080721130298351124003203 13621081695447526686004805)
                  ·
                    refine ⟨2553952817896411253625901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13621081695447526686004805 2553952817896411253625901)
                    ·
                      refine ⟨957732306711154220109713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2553952817896411253625901 957732306711154220109713)
                      ·
                        rfl

theorem cell23_1865177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 4, 3].length) (baseStart_1865177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1865177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1865177 prefixEnd_1865177 := by exact prefixLift 1865177
  have htrace : WordTrace (prefixWord ++ tailWord_1865177) baseStart_1865177 baseEnd_1865177 := by
    simpa [prefixWord, tailWord_1865177, baseEnd_1865177] using wordTrace_append hprefix tailTrace_1865177
  have hstable : (prefixWord ++ tailWord_1865177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865177).length < 2 ^ (prefixWord ++ tailWord_1865177).sum := by decide
  have hdescent : baseEnd_1865177 < baseStart_1865177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865184 : List Nat := [2, 1, 1, 3, 1, 1, 2, 7, 1, 4]
def baseStart_1865184 : Nat := 118140960795 + 1865184 * 2 ^ 59
def prefixEnd_1865184 : Nat := 4983230072969 + 3 ^ 40 * 1865184 * 2
def baseEnd_1865184 : Nat := 319245300358578564240727

theorem tailTrace_1865184 : CollatzResearch.WordTrace tailWord_1865184 prefixEnd_1865184 319245300358578564240727 := by
  unfold tailWord_1865184
  simp only [CollatzResearch.WordTrace]
  refine ⟨34014424637382195455701303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45352566183176260607601737 34014424637382195455701303)
  ·
    refine ⟨51021636956073293183551955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34014424637382195455701303 51021636956073293183551955)
    ·
      refine ⟨76532455434109939775327933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51021636956073293183551955 76532455434109939775327933)
      ·
        refine ⟨28699670787791227415747975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76532455434109939775327933 28699670787791227415747975)
        ·
          refine ⟨43049506181686841123621963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28699670787791227415747975 43049506181686841123621963)
          ·
            refine ⟨64574259272530261685432945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43049506181686841123621963 64574259272530261685432945)
            ·
              refine ⟨48430694454397696264074709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64574259272530261685432945 48430694454397696264074709)
              ·
                refine ⟨1135094401274946006189251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 48430694454397696264074709 1135094401274946006189251)
                ·
                  refine ⟨1702641601912419009283877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1135094401274946006189251 1702641601912419009283877)
                  ·
                    refine ⟨319245300358578564240727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1702641601912419009283877 319245300358578564240727)
                    ·
                      rfl

theorem cell23_1865184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 7, 1, 4].length) (baseStart_1865184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1865184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1865184 prefixEnd_1865184 := by exact prefixLift 1865184
  have htrace : WordTrace (prefixWord ++ tailWord_1865184) baseStart_1865184 baseEnd_1865184 := by
    simpa [prefixWord, tailWord_1865184, baseEnd_1865184] using wordTrace_append hprefix tailTrace_1865184
  have hstable : (prefixWord ++ tailWord_1865184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865184).length < 2 ^ (prefixWord ++ tailWord_1865184).sum := by decide
  have hdescent : baseEnd_1865184 < baseStart_1865184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865224 : List Nat := [2, 1, 3, 2, 1, 1, 2, 4, 3, 1, 3]
def baseStart_1865224 : Nat := 118140960795 + 1865224 * 2 ^ 59
def prefixEnd_1865224 : Nat := 4983230072969 + 3 ^ 40 * 1865224 * 2
def baseEnd_1865224 : Nat := 957756440301915536221997

theorem tailTrace_1865224 : CollatzResearch.WordTrace tailWord_1865224 prefixEnd_1865224 957756440301915536221997 := by
  unfold tailWord_1865224
  simp only [CollatzResearch.WordTrace]
  refine ⟨34015154097309738871429363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45353538796412985161905817 34015154097309738871429363)
  ·
    refine ⟨51022731145964608307144045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34015154097309738871429363 51022731145964608307144045)
    ·
      refine ⟨19133524179736728115179017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51022731145964608307144045 19133524179736728115179017)
      ·
        refine ⟨14350143134802546086384263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19133524179736728115179017 14350143134802546086384263)
        ·
          refine ⟨21525214702203819129576395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14350143134802546086384263 21525214702203819129576395)
          ·
            refine ⟨32287822053305728694364593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21525214702203819129576395 32287822053305728694364593)
            ·
              refine ⟨24215866539979296520773445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32287822053305728694364593 24215866539979296520773445)
              ·
                refine ⟨4540474976246118097645021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24215866539979296520773445 4540474976246118097645021)
                ·
                  refine ⟨1702678116092294286616883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4540474976246118097645021 1702678116092294286616883)
                  ·
                    refine ⟨2554017174138441429925325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1702678116092294286616883 2554017174138441429925325)
                    ·
                      refine ⟨957756440301915536221997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2554017174138441429925325 957756440301915536221997)
                      ·
                        rfl

theorem cell23_1865224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4, 3, 1, 3].length) (baseStart_1865224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1865224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1865224 prefixEnd_1865224 := by exact prefixLift 1865224
  have htrace : WordTrace (prefixWord ++ tailWord_1865224) baseStart_1865224 baseEnd_1865224 := by
    simpa [prefixWord, tailWord_1865224, baseEnd_1865224] using wordTrace_append hprefix tailTrace_1865224
  have hstable : (prefixWord ++ tailWord_1865224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865224).length < 2 ^ (prefixWord ++ tailWord_1865224).sum := by decide
  have hdescent : baseEnd_1865224 < baseStart_1865224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865258 : List Nat := [3, 1, 4, 1, 1, 1, 3, 4, 1, 1, 3]
def baseStart_1865258 : Nat := 118140960795 + 1865258 * 2 ^ 59
def prefixEnd_1865258 : Nat := 4983230072969 + 3 ^ 40 * 1865258 * 2
def baseEnd_1865258 : Nat := 957773898644168403196841

theorem tailTrace_1865258 : CollatzResearch.WordTrace tailWord_1865258 prefixEnd_1865258 957773898644168403196841 := by
  unfold tailWord_1865258
  simp only [CollatzResearch.WordTrace]
  refine ⟨17007887069124075387399107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45354365517664201033064285 17007887069124075387399107)
  ·
    refine ⟨25511830603686113081098661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17007887069124075387399107 25511830603686113081098661)
    ·
      refine ⟨4783468238191146202705999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25511830603686113081098661 4783468238191146202705999)
      ·
        refine ⟨7175202357286719304058999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4783468238191146202705999 7175202357286719304058999)
        ·
          refine ⟨10762803535930078956088499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7175202357286719304058999 10762803535930078956088499)
          ·
            refine ⟨16144205303895118434132749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10762803535930078956088499 16144205303895118434132749)
            ·
              refine ⟨6054076988960669412799781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16144205303895118434132749 6054076988960669412799781)
              ·
                refine ⟨1135139435430125514899959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6054076988960669412799781 1135139435430125514899959)
                ·
                  refine ⟨1702709153145188272349939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1135139435430125514899959 1702709153145188272349939)
                  ·
                    refine ⟨2554063729717782408524909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1702709153145188272349939 2554063729717782408524909)
                    ·
                      refine ⟨957773898644168403196841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2554063729717782408524909 957773898644168403196841)
                      ·
                        rfl

theorem cell23_1865258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_1865258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1865258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1865258 prefixEnd_1865258 := by exact prefixLift 1865258
  have htrace : WordTrace (prefixWord ++ tailWord_1865258) baseStart_1865258 baseEnd_1865258 := by
    simpa [prefixWord, tailWord_1865258, baseEnd_1865258] using wordTrace_append hprefix tailTrace_1865258
  have hstable : (prefixWord ++ tailWord_1865258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865258).length < 2 ^ (prefixWord ++ tailWord_1865258).sum := by decide
  have hdescent : baseEnd_1865258 < baseStart_1865258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865274 : List Nat := [3, 1, 1, 1, 3, 2, 1, 5, 2, 4]
def baseStart_1865274 : Nat := 118140960795 + 1865274 * 2 ^ 59
def prefixEnd_1865274 : Nat := 4983230072969 + 3 ^ 40 * 1865274 * 2
def baseEnd_1865274 : Nat := 319260704778213446865589

theorem tailTrace_1865274 : CollatzResearch.WordTrace tailWord_1865274 prefixEnd_1865274 319260704778213446865589 := by
  unfold tailWord_1865274
  simp only [CollatzResearch.WordTrace]
  refine ⟨17008032961109584070544719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45354754562958890854785917 17008032961109584070544719)
  ·
    refine ⟨25512049441664376105817079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17008032961109584070544719 25512049441664376105817079)
    ·
      refine ⟨38268074162496564158725619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25512049441664376105817079 38268074162496564158725619)
      ·
        refine ⟨57402111243744846238088429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38268074162496564158725619 57402111243744846238088429)
        ·
          refine ⟨21525791716404317339283161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57402111243744846238088429 21525791716404317339283161)
          ·
            refine ⟨16144343787303238004462371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21525791716404317339283161 16144343787303238004462371)
            ·
              refine ⟨24216515680954857006693557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16144343787303238004462371 24216515680954857006693557)
              ·
                refine ⟨2270298345089517844377521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24216515680954857006693557 2270298345089517844377521)
                ·
                  refine ⟨1702723758817138383283141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2270298345089517844377521 1702723758817138383283141)
                  ·
                    refine ⟨319260704778213446865589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1702723758817138383283141 319260704778213446865589)
                    ·
                      rfl

theorem cell23_1865274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 5, 2, 4].length) (baseStart_1865274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1865274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1865274 prefixEnd_1865274 := by exact prefixLift 1865274
  have htrace : WordTrace (prefixWord ++ tailWord_1865274) baseStart_1865274 baseEnd_1865274 := by
    simpa [prefixWord, tailWord_1865274, baseEnd_1865274] using wordTrace_append hprefix tailTrace_1865274
  have hstable : (prefixWord ++ tailWord_1865274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865274).length < 2 ^ (prefixWord ++ tailWord_1865274).sum := by decide
  have hdescent : baseEnd_1865274 < baseStart_1865274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865298 : List Nat := [3, 2, 2, 1, 2, 4, 2, 1, 1, 1, 4]
def baseStart_1865298 : Nat := 118140960795 + 1865298 * 2 ^ 59
def prefixEnd_1865298 : Nat := 4983230072969 + 3 ^ 40 * 1865298 * 2
def baseEnd_1865298 : Nat := 957794437870348246696657

theorem tailTrace_1865298 : CollatzResearch.WordTrace tailWord_1865298 prefixEnd_1865298 957794437870348246696657 := by
  unfold tailWord_1865298
  simp only [CollatzResearch.WordTrace]
  refine ⟨17008251799087847095263137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45355338130900925587368365 17008251799087847095263137)
  ·
    refine ⟨12756188849315885321447353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17008251799087847095263137 12756188849315885321447353)
    ·
      refine ⟨9567141636986913991085515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12756188849315885321447353 9567141636986913991085515)
      ·
        refine ⟨14350712455480370986628273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9567141636986913991085515 14350712455480370986628273)
        ·
          refine ⟨10763034341610278239971205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14350712455480370986628273 10763034341610278239971205)
          ·
            refine ⟨2018068939051927169994601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10763034341610278239971205 2018068939051927169994601)
            ·
              refine ⟨1513551704288945377495951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2018068939051927169994601 1513551704288945377495951)
              ·
                refine ⟨2270327556433418066243927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1513551704288945377495951 2270327556433418066243927)
                ·
                  refine ⟨3405491334650127099365891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2270327556433418066243927 3405491334650127099365891)
                  ·
                    refine ⟨5108237001975190649048837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3405491334650127099365891 5108237001975190649048837)
                    ·
                      refine ⟨957794437870348246696657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5108237001975190649048837 957794437870348246696657)
                      ·
                        rfl

theorem cell23_1865298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2, 1, 1, 1, 4].length) (baseStart_1865298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1865298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1865298 prefixEnd_1865298 := by exact prefixLift 1865298
  have htrace : WordTrace (prefixWord ++ tailWord_1865298) baseStart_1865298 baseEnd_1865298 := by
    simpa [prefixWord, tailWord_1865298, baseEnd_1865298] using wordTrace_append hprefix tailTrace_1865298
  have hstable : (prefixWord ++ tailWord_1865298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865298).length < 2 ^ (prefixWord ++ tailWord_1865298).sum := by decide
  have hdescent : baseEnd_1865298 < baseStart_1865298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865308 : List Nat := [2, 2, 4, 1, 2, 3, 1, 2, 2, 4]
def baseStart_1865308 : Nat := 118140960795 + 1865308 * 2 ^ 59
def prefixEnd_1865308 : Nat := 4983230072969 + 3 ^ 40 * 1865308 * 2
def baseEnd_1865308 : Nat := 319266524225631069190537

theorem tailTrace_1865308 : CollatzResearch.WordTrace tailWord_1865308 prefixEnd_1865308 319266524225631069190537 := by
  unfold tailWord_1865308
  simp only [CollatzResearch.WordTrace]
  refine ⟨34016685963157580044458289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45355581284210106725944385 34016685963157580044458289)
  ·
    refine ⟨25512514472368185033343717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34016685963157580044458289 25512514472368185033343717)
    ·
      refine ⟨4783596463569034693751947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25512514472368185033343717 4783596463569034693751947)
      ·
        refine ⟨7175394695353552040627921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4783596463569034693751947 7175394695353552040627921)
        ·
          refine ⟨5381546021515164030470941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7175394695353552040627921 5381546021515164030470941)
          ·
            refine ⟨2018079758068186511426603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5381546021515164030470941 2018079758068186511426603)
            ·
              refine ⟨3027119637102279767139905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2018079758068186511426603 3027119637102279767139905)
              ·
                refine ⟨2270339727826709825354929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3027119637102279767139905 2270339727826709825354929)
                ·
                  refine ⟨1702754795870032369016197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2270339727826709825354929 1702754795870032369016197)
                  ·
                    refine ⟨319266524225631069190537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1702754795870032369016197 319266524225631069190537)
                    ·
                      rfl

theorem cell23_1865308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_1865308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1865308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1865308 prefixEnd_1865308 := by exact prefixLift 1865308
  have htrace : WordTrace (prefixWord ++ tailWord_1865308) baseStart_1865308 baseEnd_1865308 := by
    simpa [prefixWord, tailWord_1865308, baseEnd_1865308] using wordTrace_append hprefix tailTrace_1865308
  have hstable : (prefixWord ++ tailWord_1865308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865308).length < 2 ^ (prefixWord ++ tailWord_1865308).sum := by decide
  have hdescent : baseEnd_1865308 < baseStart_1865308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865358 : List Nat := [4, 1, 1, 3, 1, 2, 2, 3, 1, 3, 2]
def baseStart_1865358 : Nat := 118140960795 + 1865358 * 2 ^ 59
def prefixEnd_1865358 : Nat := 4983230072969 + 3 ^ 40 * 1865358 * 2
def baseEnd_1865358 : Nat := 957825246709618011946381

theorem tailTrace_1865358 : CollatzResearch.WordTrace tailWord_1865358 prefixEnd_1865358 957825246709618011946381 := by
  unfold tailWord_1865358
  simp only [CollatzResearch.WordTrace]
  refine ⟨8504399447016752328529591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45356797050756012418824485 8504399447016752328529591)
  ·
    refine ⟨12756599170525128492794387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8504399447016752328529591 12756599170525128492794387)
    ·
      refine ⟨19134898755787692739191581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12756599170525128492794387 19134898755787692739191581)
      ·
        refine ⟨7175587033420384777196843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19134898755787692739191581 7175587033420384777196843)
        ·
          refine ⟨10763380550130577165795265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7175587033420384777196843 10763380550130577165795265)
          ·
            refine ⟨8072535412597932874346449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10763380550130577165795265 8072535412597932874346449)
            ·
              refine ⟨6054401559448449655759837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8072535412597932874346449 6054401559448449655759837)
              ·
                refine ⟨2270400584793168620909939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6054401559448449655759837 2270400584793168620909939)
                ·
                  refine ⟨3405600877189752931364909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2270400584793168620909939 3405600877189752931364909)
                  ·
                    refine ⟨1277100328946157349261841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3405600877189752931364909 1277100328946157349261841)
                    ·
                      refine ⟨957825246709618011946381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1277100328946157349261841 957825246709618011946381)
                      ·
                        rfl

theorem cell23_1865358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_1865358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1865358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1865358 prefixEnd_1865358 := by exact prefixLift 1865358
  have htrace : WordTrace (prefixWord ++ tailWord_1865358) baseStart_1865358 baseEnd_1865358 := by
    simpa [prefixWord, tailWord_1865358, baseEnd_1865358] using wordTrace_append hprefix tailTrace_1865358
  have hstable : (prefixWord ++ tailWord_1865358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865358).length < 2 ^ (prefixWord ++ tailWord_1865358).sum := by decide
  have hdescent : baseEnd_1865358 < baseStart_1865358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865428 : List Nat := [2, 4, 1, 3, 1, 2, 1, 4, 5]
def baseStart_1865428 : Nat := 118140960795 + 1865428 * 2 ^ 59
def prefixEnd_1865428 : Nat := 4983230072969 + 3 ^ 40 * 1865428 * 2
def baseEnd_1865428 : Nat := 106429021150603637563451

theorem tailTrace_1865428 : CollatzResearch.WordTrace tailWord_1865428 prefixEnd_1865428 106429021150603637563451 := by
  unfold tailWord_1865428
  simp only [CollatzResearch.WordTrace]
  refine ⟨34018874342940210291642469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45358499123920280388856625 34018874342940210291642469)
  ·
    refine ⟨6378538939301289429682963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34018874342940210291642469 6378538939301289429682963)
    ·
      refine ⟨9567808408951934144524445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6378538939301289429682963 9567808408951934144524445)
      ·
        refine ⟨3587928153356975304196667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9567808408951934144524445 3587928153356975304196667)
        ·
          refine ⟨5381892230035462956295001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3587928153356975304196667 5381892230035462956295001)
          ·
            refine ⟨4036419172526597217221251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5381892230035462956295001 4036419172526597217221251)
            ·
              refine ⟨6054628758789895825831877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4036419172526597217221251 6054628758789895825831877)
              ·
                refine ⟨1135242892273105467343477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6054628758789895825831877 1135242892273105467343477)
                ·
                  refine ⟨106429021150603637563451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1135242892273105467343477 106429021150603637563451)
                  ·
                    rfl

theorem cell23_1865428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 4, 5].length) (baseStart_1865428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1865428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1865428 prefixEnd_1865428 := by exact prefixLift 1865428
  have htrace : WordTrace (prefixWord ++ tailWord_1865428) baseStart_1865428 baseEnd_1865428 := by
    simpa [prefixWord, tailWord_1865428, baseEnd_1865428] using wordTrace_append hprefix tailTrace_1865428
  have hstable : (prefixWord ++ tailWord_1865428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865428).length < 2 ^ (prefixWord ++ tailWord_1865428).sum := by decide
  have hdescent : baseEnd_1865428 < baseStart_1865428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865434 : List Nat := [3, 1, 1, 2, 2, 3, 2, 1, 1, 2, 5]
def baseStart_1865434 : Nat := 118140960795 + 1865434 * 2 ^ 59
def prefixEnd_1865434 : Nat := 4983230072969 + 3 ^ 40 * 1865434 * 2
def baseEnd_1865434 : Nat := 957864271239359714596031

theorem tailTrace_1865434 : CollatzResearch.WordTrace tailWord_1865434 prefixEnd_1865434 957864271239359714596031 := by
  unfold tailWord_1865434
  simp only [CollatzResearch.WordTrace]
  refine ⟨17009491880964670902000839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45358645015905789072002237 17009491880964670902000839)
  ·
    refine ⟨25514237821447006353001259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17009491880964670902000839 25514237821447006353001259)
    ·
      refine ⟨38271356732170509529501889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25514237821447006353001259 38271356732170509529501889)
      ·
        refine ⟨28703517549127882147126417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38271356732170509529501889 28703517549127882147126417)
        ·
          refine ⟨21527638161845911610344813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28703517549127882147126417 21527638161845911610344813)
          ·
            refine ⟨8072864310692216853879305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21527638161845911610344813 8072864310692216853879305)
            ·
              refine ⟨6054648233019162640409479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8072864310692216853879305 6054648233019162640409479)
              ·
                refine ⟨9081972349528743960614219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6054648233019162640409479 9081972349528743960614219)
                ·
                  refine ⟨13622958524293115940921329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9081972349528743960614219 13622958524293115940921329)
                  ·
                    refine ⟨10217218893219836955690997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13622958524293115940921329 10217218893219836955690997)
                    ·
                      refine ⟨957864271239359714596031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10217218893219836955690997 957864271239359714596031)
                      ·
                        rfl

theorem cell23_1865434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_1865434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1865434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1865434 prefixEnd_1865434 := by exact prefixLift 1865434
  have htrace : WordTrace (prefixWord ++ tailWord_1865434) baseStart_1865434 baseEnd_1865434 := by
    simpa [prefixWord, tailWord_1865434, baseEnd_1865434] using wordTrace_append hprefix tailTrace_1865434
  have hstable : (prefixWord ++ tailWord_1865434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865434).length < 2 ^ (prefixWord ++ tailWord_1865434).sum := by decide
  have hdescent : baseEnd_1865434 < baseStart_1865434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865444 : List Nat := [2, 3, 1, 1, 1, 3, 2, 2, 1, 3, 4]
def baseStart_1865444 : Nat := 118140960795 + 1865444 * 2 ^ 59
def prefixEnd_1865444 : Nat := 4983230072969 + 3 ^ 40 * 1865444 * 2
def baseEnd_1865444 : Nat := 957869406045904675470985

theorem tailTrace_1865444 : CollatzResearch.WordTrace tailWord_1865444 prefixEnd_1865444 957869406045904675470985 := by
  unfold tailWord_1865444
  simp only [CollatzResearch.WordTrace]
  refine ⟨34019166126911227657933693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45358888169214970210578257 34019166126911227657933693)
  ·
    refine ⟨12757187297591710371725135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34019166126911227657933693 12757187297591710371725135)
    ·
      refine ⟨19135780946387565557587703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12757187297591710371725135 19135780946387565557587703)
      ·
        refine ⟨28703671419581348336381555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19135780946387565557587703 28703671419581348336381555)
        ·
          refine ⟨43055507129372022504572333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28703671419581348336381555 43055507129372022504572333)
          ·
            refine ⟨16145815173514508439214625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43055507129372022504572333 16145815173514508439214625)
            ·
              refine ⟨12109361380135881329410969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16145815173514508439214625 12109361380135881329410969)
              ·
                refine ⟨9082021035101910997058227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12109361380135881329410969 9082021035101910997058227)
                ·
                  refine ⟨13623031552652866495587341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9082021035101910997058227 13623031552652866495587341)
                  ·
                    refine ⟨5108636832244824935845253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13623031552652866495587341 5108636832244824935845253)
                    ·
                      refine ⟨957869406045904675470985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5108636832244824935845253 957869406045904675470985)
                      ·
                        rfl

theorem cell23_1865444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_1865444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1865444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1865444 prefixEnd_1865444 := by exact prefixLift 1865444
  have htrace : WordTrace (prefixWord ++ tailWord_1865444) baseStart_1865444 baseEnd_1865444 := by
    simpa [prefixWord, tailWord_1865444, baseEnd_1865444] using wordTrace_append hprefix tailTrace_1865444
  have hstable : (prefixWord ++ tailWord_1865444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865444).length < 2 ^ (prefixWord ++ tailWord_1865444).sum := by decide
  have hdescent : baseEnd_1865444 < baseStart_1865444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865504 : List Nat := [2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 6]
def baseStart_1865504 : Nat := 118140960795 + 1865504 * 2 ^ 59
def prefixEnd_1865504 : Nat := 4983230072969 + 3 ^ 40 * 1865504 * 2
def baseEnd_1865504 : Nat := 957900214885174440720709

theorem tailTrace_1865504 : CollatzResearch.WordTrace tailWord_1865504 prefixEnd_1865504 957900214885174440720709 := by
  unfold tailWord_1865504
  simp only [CollatzResearch.WordTrace]
  refine ⟨34020260316802542781525783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45360347089070057042034377 34020260316802542781525783)
  ·
    refine ⟨51030390475203814172288675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34020260316802542781525783 51030390475203814172288675)
    ·
      refine ⟨76545585712805721258433013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51030390475203814172288675 76545585712805721258433013)
      ·
        refine ⟨7176148660575536367978095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76545585712805721258433013 7176148660575536367978095)
        ·
          refine ⟨10764222990863304551967143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7176148660575536367978095 10764222990863304551967143)
          ·
            refine ⟨16146334486294956827950715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10764222990863304551967143 16146334486294956827950715)
            ·
              refine ⟨24219501729442435241926073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16146334486294956827950715 24219501729442435241926073)
              ·
                refine ⟨18164626297081826431444555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24219501729442435241926073 18164626297081826431444555)
                ·
                  refine ⟨27246939445622739647166833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18164626297081826431444555 27246939445622739647166833)
                  ·
                    refine ⟨20435204584217054735375125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27246939445622739647166833 20435204584217054735375125)
                    ·
                      refine ⟨957900214885174440720709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20435204584217054735375125 957900214885174440720709)
                      ·
                        rfl

theorem cell23_1865504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_1865504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1865504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1865504 prefixEnd_1865504 := by exact prefixLift 1865504
  have htrace : WordTrace (prefixWord ++ tailWord_1865504) baseStart_1865504 baseEnd_1865504 := by
    simpa [prefixWord, tailWord_1865504, baseEnd_1865504] using wordTrace_append hprefix tailTrace_1865504
  have hstable : (prefixWord ++ tailWord_1865504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865504).length < 2 ^ (prefixWord ++ tailWord_1865504).sum := by decide
  have hdescent : baseEnd_1865504 < baseStart_1865504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865568 : List Nat := [2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 4]
def baseStart_1865568 : Nat := 118140960795 + 1865568 * 2 ^ 59
def prefixEnd_1865568 : Nat := 4983230072969 + 3 ^ 40 * 1865568 * 2
def baseEnd_1865568 : Nat := 957933077647062190320415

theorem tailTrace_1865568 : CollatzResearch.WordTrace tailWord_1865568 prefixEnd_1865568 957933077647062190320415 := by
  unfold tailWord_1865568
  simp only [CollatzResearch.WordTrace]
  refine ⟨34021427452686612246690679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45361903270248816328920905 34021427452686612246690679)
  ·
    refine ⟨51032141179029918370036019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34021427452686612246690679 51032141179029918370036019)
    ·
      refine ⟨76548211768544877555054029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51032141179029918370036019 76548211768544877555054029)
      ·
        refine ⟨28705579413204329083145261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76548211768544877555054029 28705579413204329083145261)
        ·
          refine ⟨10764592279951623406179473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28705579413204329083145261 10764592279951623406179473)
          ·
            refine ⟨8073444209963717554634605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10764592279951623406179473 8073444209963717554634605)
            ·
              refine ⟨3027541578736394082987977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8073444209963717554634605 3027541578736394082987977)
              ·
                refine ⟨2270656184052295562240983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3027541578736394082987977 2270656184052295562240983)
                ·
                  refine ⟨3405984276078443343361475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2270656184052295562240983 3405984276078443343361475)
                  ·
                    refine ⟨5108976414117665015042213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3405984276078443343361475 5108976414117665015042213)
                    ·
                      refine ⟨957933077647062190320415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5108976414117665015042213 957933077647062190320415)
                      ·
                        rfl

theorem cell23_1865568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 4].length) (baseStart_1865568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1865568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1865568 prefixEnd_1865568 := by exact prefixLift 1865568
  have htrace : WordTrace (prefixWord ++ tailWord_1865568) baseStart_1865568 baseEnd_1865568 := by
    simpa [prefixWord, tailWord_1865568, baseEnd_1865568] using wordTrace_append hprefix tailTrace_1865568
  have hstable : (prefixWord ++ tailWord_1865568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865568).length < 2 ^ (prefixWord ++ tailWord_1865568).sum := by decide
  have hdescent : baseEnd_1865568 < baseStart_1865568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865581 : List Nat := [1, 5, 1, 1, 1, 1, 3, 1, 3, 2, 4]
def baseStart_1865581 : Nat := 118140960795 + 1865581 * 2 ^ 59
def prefixEnd_1865581 : Nat := 4983230072969 + 3 ^ 40 * 1865581 * 2
def baseEnd_1865581 : Nat := 957939752895570639457855

theorem tailTrace_1865581 : CollatzResearch.WordTrace tailWord_1865581 prefixEnd_1865581 957939752895570639457855 := by
  unfold tailWord_1865581
  simp only [CollatzResearch.WordTrace]
  refine ⟨68043329054326127713604597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45362219369550751809069731 68043329054326127713604597)
  ·
    refine ⟨6379062098843074473150431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68043329054326127713604597 6379062098843074473150431)
    ·
      refine ⟨9568593148264611709725647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6379062098843074473150431 9568593148264611709725647)
      ·
        refine ⟨14352889722396917564588471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9568593148264611709725647 14352889722396917564588471)
        ·
          refine ⟨21529334583595376346882707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14352889722396917564588471 21529334583595376346882707)
          ·
            refine ⟨32294001875393064520324061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21529334583595376346882707 32294001875393064520324061)
            ·
              refine ⟨12110250703272399195121523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32294001875393064520324061 12110250703272399195121523)
              ·
                refine ⟨18165376054908598792682285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12110250703272399195121523 18165376054908598792682285)
                ·
                  refine ⟨6812016020590724547255857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18165376054908598792682285 6812016020590724547255857)
                  ·
                    refine ⟨5109012015443043410441893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6812016020590724547255857 5109012015443043410441893)
                    ·
                      refine ⟨957939752895570639457855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5109012015443043410441893 957939752895570639457855)
                      ·
                        rfl

theorem cell23_1865581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_1865581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1865581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1865581 prefixEnd_1865581 := by exact prefixLift 1865581
  have htrace : WordTrace (prefixWord ++ tailWord_1865581) baseStart_1865581 baseEnd_1865581 := by
    simpa [prefixWord, tailWord_1865581, baseEnd_1865581] using wordTrace_append hprefix tailTrace_1865581
  have hstable : (prefixWord ++ tailWord_1865581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865581).length < 2 ^ (prefixWord ++ tailWord_1865581).sum := by decide
  have hdescent : baseEnd_1865581 < baseStart_1865581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865608 : List Nat := [2, 1, 3, 3, 3, 2, 1, 8]
def baseStart_1865608 : Nat := 118140960795 + 1865608 * 2 ^ 59
def prefixEnd_1865608 : Nat := 4983230072969 + 3 ^ 40 * 1865608 * 2
def baseEnd_1865608 : Nat := 35479763587897853104453

theorem tailTrace_1865608 : CollatzResearch.WordTrace tailWord_1865608 prefixEnd_1865608 35479763587897853104453 := by
  unfold tailWord_1865608
  simp only [CollatzResearch.WordTrace]
  refine ⟨34022156912614155662418739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45362875883485540883224985 34022156912614155662418739)
  ·
    refine ⟨51033235368921233493628109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34022156912614155662418739 51033235368921233493628109)
    ·
      refine ⟨19137463263345462560110541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51033235368921233493628109 19137463263345462560110541)
      ·
        refine ⟨7176548723754548460041453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19137463263345462560110541 7176548723754548460041453)
        ·
          refine ⟨2691205771407955672515545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7176548723754548460041453 2691205771407955672515545)
          ·
            refine ⟨2018404328555966754386659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2691205771407955672515545 2018404328555966754386659)
            ·
              refine ⟨3027606492833950131579989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2018404328555966754386659 3027606492833950131579989)
              ·
                refine ⟨35479763587897853104453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3027606492833950131579989 35479763587897853104453)
                ·
                  rfl

theorem cell23_1865608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 8].length) (baseStart_1865608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1865608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1865608 prefixEnd_1865608 := by exact prefixLift 1865608
  have htrace : WordTrace (prefixWord ++ tailWord_1865608) baseStart_1865608 baseEnd_1865608 := by
    simpa [prefixWord, tailWord_1865608, baseEnd_1865608] using wordTrace_append hprefix tailTrace_1865608
  have hstable : (prefixWord ++ tailWord_1865608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865608).length < 2 ^ (prefixWord ++ tailWord_1865608).sum := by decide
  have hdescent : baseEnd_1865608 < baseStart_1865608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865646 : List Nat := [4, 1, 5, 1, 1, 2, 1, 2, 2, 4]
def baseStart_1865646 : Nat := 118140960795 + 1865646 * 2 ^ 59
def prefixEnd_1865646 : Nat := 4983230072969 + 3 ^ 40 * 1865646 * 2
def baseEnd_1865646 : Nat := 319324376379370961715019

theorem tailTrace_1865646 : CollatzResearch.WordTrace tailWord_1865646 prefixEnd_1865646 319324376379370961715019 := by
  unfold tailWord_1865646
  simp only [CollatzResearch.WordTrace]
  refine ⟨8505712474886330476840099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45363799866060429209813861 8505712474886330476840099)
  ·
    refine ⟨12758568712329495715260149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8505712474886330476840099 12758568712329495715260149)
    ·
      refine ⟨1196115816780890223305639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12758568712329495715260149 1196115816780890223305639)
      ·
        refine ⟨1794173725171335334958459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1196115816780890223305639 1794173725171335334958459)
        ·
          refine ⟨2691260587757003002437689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1794173725171335334958459 2691260587757003002437689)
          ·
            refine ⟨2018445440817752251828267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2691260587757003002437689 2018445440817752251828267)
            ·
              refine ⟨3027668161226628377742401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2018445440817752251828267 3027668161226628377742401)
              ·
                refine ⟨2270751120919971283306801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3027668161226628377742401 2270751120919971283306801)
                ·
                  refine ⟨1703063340689978462480101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2270751120919971283306801 1703063340689978462480101)
                  ·
                    refine ⟨319324376379370961715019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1703063340689978462480101 319324376379370961715019)
                    ·
                      rfl

theorem cell23_1865646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_1865646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1865646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1865646 prefixEnd_1865646 := by exact prefixLift 1865646
  have htrace : WordTrace (prefixWord ++ tailWord_1865646) baseStart_1865646 baseEnd_1865646 := by
    simpa [prefixWord, tailWord_1865646, baseEnd_1865646] using wordTrace_append hprefix tailTrace_1865646
  have hstable : (prefixWord ++ tailWord_1865646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865646).length < 2 ^ (prefixWord ++ tailWord_1865646).sum := by decide
  have hdescent : baseEnd_1865646 < baseStart_1865646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865721 : List Nat := [1, 2, 1, 3, 1, 4, 1, 1, 1, 1, 7]
def baseStart_1865721 : Nat := 118140960795 + 1865721 * 2 ^ 59
def prefixEnd_1865721 : Nat := 4983230072969 + 3 ^ 40 * 1865721 * 2
def baseEnd_1865721 : Nat := 958011640187200091707211

theorem tailTrace_1865721 : CollatzResearch.WordTrace tailWord_1865721 prefixEnd_1865721 958011640187200091707211 := by
  unfold tailWord_1865721
  simp only [CollatzResearch.WordTrace]
  refine ⟨68048435273818931623701017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45365623515879287749134011 68048435273818931623701017)
  ·
    refine ⟨51036326455364198717775763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68048435273818931623701017 51036326455364198717775763)
    ·
      refine ⟨76554489683046298076663645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51036326455364198717775763 76554489683046298076663645)
      ·
        refine ⟨28707933631142361778748867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76554489683046298076663645 28707933631142361778748867)
        ·
          refine ⟨43061900446713542668123301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28707933631142361778748867 43061900446713542668123301)
          ·
            refine ⟨8074106333758789250273119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43061900446713542668123301 8074106333758789250273119)
            ·
              refine ⟨12111159500638183875409679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8074106333758789250273119 12111159500638183875409679)
              ·
                refine ⟨18166739250957275813114519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12111159500638183875409679 18166739250957275813114519)
                ·
                  refine ⟨27250108876435913719671779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18166739250957275813114519 27250108876435913719671779)
                  ·
                    refine ⟨40875163314653870579507669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27250108876435913719671779 40875163314653870579507669)
                    ·
                      refine ⟨958011640187200091707211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 40875163314653870579507669 958011640187200091707211)
                      ·
                        rfl

theorem cell23_1865721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_1865721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1865721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1865721 prefixEnd_1865721 := by exact prefixLift 1865721
  have htrace : WordTrace (prefixWord ++ tailWord_1865721) baseStart_1865721 baseEnd_1865721 := by
    simpa [prefixWord, tailWord_1865721, baseEnd_1865721] using wordTrace_append hprefix tailTrace_1865721
  have hstable : (prefixWord ++ tailWord_1865721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865721).length < 2 ^ (prefixWord ++ tailWord_1865721).sum := by decide
  have hdescent : baseEnd_1865721 < baseStart_1865721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865726 : List Nat := [4, 2, 2, 2, 1, 1, 4, 1, 2, 2, 2]
def baseStart_1865726 : Nat := 118140960795 + 1865726 * 2 ^ 59
def prefixEnd_1865726 : Nat := 4983230072969 + 3 ^ 40 * 1865726 * 2
def baseEnd_1865726 : Nat := 958014207590472572144689

theorem tailTrace_1865726 : CollatzResearch.WordTrace tailWord_1865726 prefixEnd_1865726 958014207590472572144689 := by
  unfold tailWord_1865726
  simp only [CollatzResearch.WordTrace]
  refine ⟨8506077204850102184704129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45365745092533878318422021 8506077204850102184704129)
  ·
    refine ⟨6379557903637576638528097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8506077204850102184704129 6379557903637576638528097)
    ·
      refine ⟨4784668427728182478896073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6379557903637576638528097 4784668427728182478896073)
      ·
        refine ⟨3588501320796136859172055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4784668427728182478896073 3588501320796136859172055)
        ·
          refine ⟨5382751981194205288758083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3588501320796136859172055 5382751981194205288758083)
          ·
            refine ⟨8074127971791307933137125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5382751981194205288758083 8074127971791307933137125)
            ·
              refine ⟨1513898994710870237463211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8074127971791307933137125 1513898994710870237463211)
              ·
                refine ⟨2270848492066305356194817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1513898994710870237463211 2270848492066305356194817)
                ·
                  refine ⟨1703136369049729017146113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2270848492066305356194817 1703136369049729017146113)
                  ·
                    refine ⟨1277352276787296762859585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1703136369049729017146113 1277352276787296762859585)
                    ·
                      refine ⟨958014207590472572144689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1277352276787296762859585 958014207590472572144689)
                      ·
                        rfl

theorem cell23_1865726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_1865726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1865726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1865726 prefixEnd_1865726 := by exact prefixLift 1865726
  have htrace : WordTrace (prefixWord ++ tailWord_1865726) baseStart_1865726 baseEnd_1865726 := by
    simpa [prefixWord, tailWord_1865726, baseEnd_1865726] using wordTrace_append hprefix tailTrace_1865726
  have hstable : (prefixWord ++ tailWord_1865726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865726).length < 2 ^ (prefixWord ++ tailWord_1865726).sum := by decide
  have hdescent : baseEnd_1865726 < baseStart_1865726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865731 : List Nat := [1, 1, 1, 3, 2, 1, 1, 3, 3, 3, 4]
def baseStart_1865731 : Nat := 118140960795 + 1865731 * 2 ^ 59
def prefixEnd_1865731 : Nat := 4983230072969 + 3 ^ 40 * 1865731 * 2
def baseEnd_1865731 : Nat := 958016774993745052582165

theorem tailTrace_1865731 : CollatzResearch.WordTrace tailWord_1865731 prefixEnd_1865731 958016774993745052582165 := by
  unfold tailWord_1865731
  simp only [CollatzResearch.WordTrace]
  refine ⟨68048800003782703331565047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45365866669188468887710031 68048800003782703331565047)
  ·
    refine ⟨102073200005674054997347571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68048800003782703331565047 102073200005674054997347571)
    ·
      refine ⟨153109800008511082496021357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102073200005674054997347571 153109800008511082496021357)
      ·
        refine ⟨57416175003191655936008009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153109800008511082496021357 57416175003191655936008009)
        ·
          refine ⟨43062131252393741952006007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57416175003191655936008009 43062131252393741952006007)
          ·
            refine ⟨64593196878590612928009011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43062131252393741952006007 64593196878590612928009011)
            ·
              refine ⟨96889795317885919392013517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64593196878590612928009011 96889795317885919392013517)
              ·
                refine ⟨36333673244207219772005069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96889795317885919392013517 36333673244207219772005069)
                ·
                  refine ⟨13625127466577707414501901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36333673244207219772005069 13625127466577707414501901)
                  ·
                    refine ⟨5109422799966640280438213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13625127466577707414501901 5109422799966640280438213)
                    ·
                      refine ⟨958016774993745052582165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5109422799966640280438213 958016774993745052582165)
                      ·
                        rfl

theorem cell23_1865731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 3, 4].length) (baseStart_1865731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1865731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1865731 prefixEnd_1865731 := by exact prefixLift 1865731
  have htrace : WordTrace (prefixWord ++ tailWord_1865731) baseStart_1865731 baseEnd_1865731 := by
    simpa [prefixWord, tailWord_1865731, baseEnd_1865731] using wordTrace_append hprefix tailTrace_1865731
  have hstable : (prefixWord ++ tailWord_1865731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865731).length < 2 ^ (prefixWord ++ tailWord_1865731).sum := by decide
  have hdescent : baseEnd_1865731 < baseStart_1865731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865782 : List Nat := [5, 1, 2, 1, 1, 1, 3, 1, 2, 4, 2]
def baseStart_1865782 : Nat := 118140960795 + 1865782 * 2 ^ 59
def prefixEnd_1865782 : Nat := 4983230072969 + 3 ^ 40 * 1865782 * 2
def baseEnd_1865782 : Nat := 958042962507124353044431

theorem tailTrace_1865782 : CollatzResearch.WordTrace tailWord_1865782 prefixEnd_1865782 958042962507124353044431 := by
  unfold tailWord_1865782
  simp only [CollatzResearch.WordTrace]
  refine ⟨4253166257912371190104475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45367106751065292694447733 4253166257912371190104475)
  ·
    refine ⟨6379749386868556785156713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4253166257912371190104475 6379749386868556785156713)
    ·
      refine ⟨4784812040151417588867535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6379749386868556785156713 4784812040151417588867535)
      ·
        refine ⟨7177218060227126383301303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4784812040151417588867535 7177218060227126383301303)
        ·
          refine ⟨10765827090340689574951955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7177218060227126383301303 10765827090340689574951955)
          ·
            refine ⟨16148740635511034362427933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10765827090340689574951955 16148740635511034362427933)
            ·
              refine ⟨6055777738316637885910475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16148740635511034362427933 6055777738316637885910475)
              ·
                refine ⟨9083666607474956828865713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6055777738316637885910475 9083666607474956828865713)
                ·
                  refine ⟨6812749955606217621649285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9083666607474956828865713 6812749955606217621649285)
                  ·
                    refine ⟨1277390616676165804059241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6812749955606217621649285 1277390616676165804059241)
                    ·
                      refine ⟨958042962507124353044431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1277390616676165804059241 958042962507124353044431)
                      ·
                        rfl

theorem cell23_1865782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_1865782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1865782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1865782 prefixEnd_1865782 := by exact prefixLift 1865782
  have htrace : WordTrace (prefixWord ++ tailWord_1865782) baseStart_1865782 baseEnd_1865782 := by
    simpa [prefixWord, tailWord_1865782, baseEnd_1865782] using wordTrace_append hprefix tailTrace_1865782
  have hstable : (prefixWord ++ tailWord_1865782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865782).length < 2 ^ (prefixWord ++ tailWord_1865782).sum := by decide
  have hdescent : baseEnd_1865782 < baseStart_1865782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865788 : List Nat := [2, 2, 2, 2, 2, 1, 1, 5, 6]
def baseStart_1865788 : Nat := 118140960795 + 1865788 * 2 ^ 59
def prefixEnd_1865788 : Nat := 4983230072969 + 3 ^ 40 * 1865788 * 2
def baseEnd_1865788 : Nat := 106449560376783481063267

theorem tailTrace_1865788 : CollatzResearch.WordTrace tailWord_1865788 prefixEnd_1865788 106449560376783481063267 := by
  unfold tailWord_1865788
  simp only [CollatzResearch.WordTrace]
  refine ⟨34025439482288101033195009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45367252643050801377593345 34025439482288101033195009)
  ·
    refine ⟨25519079611716075774896257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34025439482288101033195009 25519079611716075774896257)
    ·
      refine ⟨19139309708787056831172193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25519079611716075774896257 19139309708787056831172193)
      ·
        refine ⟨14354482281590292623379145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19139309708787056831172193 14354482281590292623379145)
        ·
          refine ⟨10765861711192719467534359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14354482281590292623379145 10765861711192719467534359)
          ·
            refine ⟨16148792566789079201301539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10765861711192719467534359 16148792566789079201301539)
            ·
              refine ⟨24223188850183618801952309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16148792566789079201301539 24223188850183618801952309)
              ·
                refine ⟨2270923954704714262683029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24223188850183618801952309 2270923954704714262683029)
                ·
                  refine ⟨106449560376783481063267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2270923954704714262683029 106449560376783481063267)
                  ·
                    rfl

theorem cell23_1865788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 5, 6].length) (baseStart_1865788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1865788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1865788 prefixEnd_1865788 := by exact prefixLift 1865788
  have htrace : WordTrace (prefixWord ++ tailWord_1865788) baseStart_1865788 baseEnd_1865788 := by
    simpa [prefixWord, tailWord_1865788, baseEnd_1865788] using wordTrace_append hprefix tailTrace_1865788
  have hstable : (prefixWord ++ tailWord_1865788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865788).length < 2 ^ (prefixWord ++ tailWord_1865788).sum := by decide
  have hdescent : baseEnd_1865788 < baseStart_1865788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865811 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 7]
def baseStart_1865811 : Nat := 118140960795 + 1865811 * 2 ^ 59
def prefixEnd_1865811 : Nat := 4983230072969 + 3 ^ 40 * 1865811 * 2
def baseEnd_1865811 : Nat := 958057853446104739581797

theorem tailTrace_1865811 : CollatzResearch.WordTrace tailWord_1865811 prefixEnd_1865811 958057853446104739581797 := by
  unfold tailWord_1865811
  simp only [CollatzResearch.WordTrace]
  refine ⟨68051717843492876994477287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45367811895661917996318191 68051717843492876994477287)
  ·
    refine ⟨102077576765239315491715931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68051717843492876994477287 102077576765239315491715931)
    ·
      refine ⟨153116365147858973237573897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102077576765239315491715931 153116365147858973237573897)
      ·
        refine ⟨114837273860894229928180423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153116365147858973237573897 114837273860894229928180423)
        ·
          refine ⟨172255910791341344892270635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114837273860894229928180423 172255910791341344892270635)
          ·
            refine ⟨258383866187012017338405953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172255910791341344892270635 258383866187012017338405953)
            ·
              refine ⟨193787899640259013003804465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 258383866187012017338405953 193787899640259013003804465)
              ·
                refine ⟨145340924730194259752853349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193787899640259013003804465 145340924730194259752853349)
                ·
                  refine ⟨27251423386911423703660003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 145340924730194259752853349 27251423386911423703660003)
                  ·
                    refine ⟨40877135080367135555490005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27251423386911423703660003 40877135080367135555490005)
                    ·
                      refine ⟨958057853446104739581797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 40877135080367135555490005 958057853446104739581797)
                      ·
                        rfl

theorem cell23_1865811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 7].length) (baseStart_1865811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1865811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1865811 prefixEnd_1865811 := by exact prefixLift 1865811
  have htrace : WordTrace (prefixWord ++ tailWord_1865811) baseStart_1865811 baseEnd_1865811 := by
    simpa [prefixWord, tailWord_1865811, baseEnd_1865811] using wordTrace_append hprefix tailTrace_1865811
  have hstable : (prefixWord ++ tailWord_1865811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865811).length < 2 ^ (prefixWord ++ tailWord_1865811).sum := by decide
  have hdescent : baseEnd_1865811 < baseStart_1865811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865825 : List Nat := [1, 2, 3, 1, 1, 2, 1, 3, 4, 3, 2]
def baseStart_1865825 : Nat := 118140960795 + 1865825 * 2 ^ 59
def prefixEnd_1865825 : Nat := 4983230072969 + 3 ^ 40 * 1865825 * 2
def baseEnd_1865825 : Nat := 958065042175267684806733

theorem tailTrace_1865825 : CollatzResearch.WordTrace tailWord_1865825 prefixEnd_1865825 958065042175267684806733 := by
  unfold tailWord_1865825
  simp only [CollatzResearch.WordTrace]
  refine ⟨68052228465442157385486929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45368152310294771590324619 68052228465442157385486929)
  ·
    refine ⟨51039171349081618039115197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68052228465442157385486929 51039171349081618039115197)
    ·
      refine ⟨19139689255905606764668199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51039171349081618039115197 19139689255905606764668199)
      ·
        refine ⟨28709533883858410147002299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19139689255905606764668199 28709533883858410147002299)
        ·
          refine ⟨43064300825787615220503449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28709533883858410147002299 43064300825787615220503449)
          ·
            refine ⟨32298225619340711415377587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43064300825787615220503449 32298225619340711415377587)
            ·
              refine ⟨48447338429011067123066381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32298225619340711415377587 48447338429011067123066381)
              ·
                refine ⟨18167751910879150171149893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48447338429011067123066381 18167751910879150171149893)
                ·
                  refine ⟨3406453483289840657090605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18167751910879150171149893 3406453483289840657090605)
                  ·
                    refine ⟨1277420056233690246408977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3406453483289840657090605 1277420056233690246408977)
                    ·
                      refine ⟨958065042175267684806733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1277420056233690246408977 958065042175267684806733)
                      ·
                        rfl

theorem cell23_1865825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 4, 3, 2].length) (baseStart_1865825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1865825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1865825 prefixEnd_1865825 := by exact prefixLift 1865825
  have htrace : WordTrace (prefixWord ++ tailWord_1865825) baseStart_1865825 baseEnd_1865825 := by
    simpa [prefixWord, tailWord_1865825, baseEnd_1865825] using wordTrace_append hprefix tailTrace_1865825
  have hstable : (prefixWord ++ tailWord_1865825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865825).length < 2 ^ (prefixWord ++ tailWord_1865825).sum := by decide
  have hdescent : baseEnd_1865825 < baseStart_1865825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865866 : List Nat := [3, 1, 2, 3, 1, 4, 1, 3, 1, 1, 3]
def baseStart_1865866 : Nat := 118140960795 + 1865866 * 2 ^ 59
def prefixEnd_1865866 : Nat := 4983230072969 + 3 ^ 40 * 1865866 * 2
def baseEnd_1865866 : Nat := 958086094882102024394045

theorem tailTrace_1865866 : CollatzResearch.WordTrace tailWord_1865866 prefixEnd_1865866 958086094882102024394045 := by
  unfold tailWord_1865866
  simp only [CollatzResearch.WordTrace]
  refine ⟨17013430964573405346932363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45369149238862414258486301 17013430964573405346932363)
  ·
    refine ⟨25520146446860108020398545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17013430964573405346932363 25520146446860108020398545)
    ·
      refine ⟨19140109835145081015298909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25520146446860108020398545 19140109835145081015298909)
      ·
        refine ⟨7177541188179405380737091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19140109835145081015298909 7177541188179405380737091)
        ·
          refine ⟨10766311782269108071105637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7177541188179405380737091 10766311782269108071105637)
          ·
            refine ⟨2018683459175457763332307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10766311782269108071105637 2018683459175457763332307)
            ·
              refine ⟨3028025188763186644998461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2018683459175457763332307 3028025188763186644998461)
              ·
                refine ⟨1135509445786194991874423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3028025188763186644998461 1135509445786194991874423)
                ·
                  refine ⟨1703264168679292487811635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1135509445786194991874423 1703264168679292487811635)
                  ·
                    refine ⟨2554896253018938731717453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1703264168679292487811635 2554896253018938731717453)
                    ·
                      refine ⟨958086094882102024394045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2554896253018938731717453 958086094882102024394045)
                      ·
                        rfl

theorem cell23_1865866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_1865866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1865866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1865866 prefixEnd_1865866 := by exact prefixLift 1865866
  have htrace : WordTrace (prefixWord ++ tailWord_1865866) baseStart_1865866 baseEnd_1865866 := by
    simpa [prefixWord, tailWord_1865866, baseEnd_1865866] using wordTrace_append hprefix tailTrace_1865866
  have hstable : (prefixWord ++ tailWord_1865866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865866).length < 2 ^ (prefixWord ++ tailWord_1865866).sum := by decide
  have hdescent : baseEnd_1865866 < baseStart_1865866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865876 : List Nat := [2, 4, 2, 3, 1, 1, 1, 2, 2, 3, 2]
def baseStart_1865876 : Nat := 118140960795 + 1865876 * 2 ^ 59
def prefixEnd_1865876 : Nat := 4983230072969 + 3 ^ 40 * 1865876 * 2
def baseEnd_1865876 : Nat := 958091229688646985268999

theorem tailTrace_1865876 : CollatzResearch.WordTrace tailWord_1865876 prefixEnd_1865876 958091229688646985268999 := by
  unfold tailWord_1865876
  simp only [CollatzResearch.WordTrace]
  refine ⟨34027044294128696547796741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45369392392171595397062321 34027044294128696547796741)
  ·
    refine ⟨6380070805149130602711889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34027044294128696547796741 6380070805149130602711889)
    ·
      refine ⟨4785053103861847952033917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6380070805149130602711889 4785053103861847952033917)
      ·
        refine ⟨1794394913948192982012719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4785053103861847952033917 1794394913948192982012719)
        ·
          refine ⟨2691592370922289473019079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1794394913948192982012719 2691592370922289473019079)
          ·
            refine ⟨4037388556383434209528619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2691592370922289473019079 4037388556383434209528619)
            ·
              refine ⟨6056082834575151314292929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4037388556383434209528619 6056082834575151314292929)
              ·
                refine ⟨4542062125931363485719697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6056082834575151314292929 4542062125931363485719697)
                ·
                  refine ⟨3406546594448522614289773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4542062125931363485719697 3406546594448522614289773)
                  ·
                    refine ⟨1277454972918195980358665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3406546594448522614289773 1277454972918195980358665)
                    ·
                      refine ⟨958091229688646985268999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1277454972918195980358665 958091229688646985268999)
                      ·
                        rfl

theorem cell23_1865876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_1865876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1865876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1865876 prefixEnd_1865876 := by exact prefixLift 1865876
  have htrace : WordTrace (prefixWord ++ tailWord_1865876) baseStart_1865876 baseEnd_1865876 := by
    simpa [prefixWord, tailWord_1865876, baseEnd_1865876] using wordTrace_append hprefix tailTrace_1865876
  have hstable : (prefixWord ++ tailWord_1865876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865876).length < 2 ^ (prefixWord ++ tailWord_1865876).sum := by decide
  have hdescent : baseEnd_1865876 < baseStart_1865876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865889 : List Nat := [1, 2, 3, 3, 1, 2, 3, 1, 3, 2, 2]
def baseStart_1865889 : Nat := 118140960795 + 1865889 * 2 ^ 59
def prefixEnd_1865889 : Nat := 4983230072969 + 3 ^ 40 * 1865889 * 2
def baseEnd_1865889 : Nat := 958097904937155434406439

theorem tailTrace_1865889 : CollatzResearch.WordTrace tailWord_1865889 prefixEnd_1865889 958097904937155434406439 := by
  unfold tailWord_1865889
  simp only [CollatzResearch.WordTrace]
  refine ⟨68054562737210296315816721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45369708491473530877211147 68054562737210296315816721)
  ·
    refine ⟨51040922052907722236862541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68054562737210296315816721 51040922052907722236862541)
    ·
      refine ⟨19140345769840395838823453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51040922052907722236862541 19140345769840395838823453)
      ·
        refine ⟨7177629663690148439558795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19140345769840395838823453 7177629663690148439558795)
        ·
          refine ⟨10766444495535222659338193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7177629663690148439558795 10766444495535222659338193)
          ·
            refine ⟨8074833371651416994503645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10766444495535222659338193 8074833371651416994503645)
            ·
              refine ⟨3028062514369281372938867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8074833371651416994503645 3028062514369281372938867)
              ·
                refine ⟨4542093771553922059408301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3028062514369281372938867 4542093771553922059408301)
                ·
                  refine ⟨1703285164332720772278113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4542093771553922059408301 1703285164332720772278113)
                  ·
                    refine ⟨1277463873249540579208585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1703285164332720772278113 1277463873249540579208585)
                    ·
                      refine ⟨958097904937155434406439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1277463873249540579208585 958097904937155434406439)
                      ·
                        rfl

theorem cell23_1865889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_1865889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1865889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1865889 prefixEnd_1865889 := by exact prefixLift 1865889
  have htrace : WordTrace (prefixWord ++ tailWord_1865889) baseStart_1865889 baseEnd_1865889 := by
    simpa [prefixWord, tailWord_1865889, baseEnd_1865889] using wordTrace_append hprefix tailTrace_1865889
  have hstable : (prefixWord ++ tailWord_1865889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865889).length < 2 ^ (prefixWord ++ tailWord_1865889).sum := by decide
  have hdescent : baseEnd_1865889 < baseStart_1865889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865909 : List Nat := [1, 3, 3, 4, 1, 1, 1, 1, 3, 2, 3]
def baseStart_1865909 : Nat := 118140960795 + 1865909 * 2 ^ 59
def prefixEnd_1865909 : Nat := 4983230072969 + 3 ^ 40 * 1865909 * 2
def baseEnd_1865909 : Nat := 958108174550245356156347

theorem tailTrace_1865909 : CollatzResearch.WordTrace tailWord_1865909 prefixEnd_1865909 958108174550245356156347 := by
  unfold tailWord_1865909
  simp only [CollatzResearch.WordTrace]
  refine ⟨68055292197137839731544781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45370194798091893154363187 68055292197137839731544781)
  ·
    refine ⟨25520734573926689899329293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68055292197137839731544781 25520734573926689899329293)
    ·
      refine ⟨9570275465222508712248485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25520734573926689899329293 9570275465222508712248485)
      ·
        refine ⟨1794426649729220383546591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9570275465222508712248485 1794426649729220383546591)
        ·
          refine ⟨2691639974593830575319887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1794426649729220383546591 2691639974593830575319887)
          ·
            refine ⟨4037459961890745862979831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2691639974593830575319887 4037459961890745862979831)
            ·
              refine ⟨6056189942836118794469747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4037459961890745862979831 6056189942836118794469747)
              ·
                refine ⟨9084284914254178191704621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6056189942836118794469747 9084284914254178191704621)
                ·
                  refine ⟨3406606842845316821889233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9084284914254178191704621 3406606842845316821889233)
                  ·
                    refine ⟨2554955132133987616416925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3406606842845316821889233 2554955132133987616416925)
                    ·
                      refine ⟨958108174550245356156347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2554955132133987616416925 958108174550245356156347)
                      ·
                        rfl

theorem cell23_1865909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_1865909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1865909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1865909 prefixEnd_1865909 := by exact prefixLift 1865909
  have htrace : WordTrace (prefixWord ++ tailWord_1865909) baseStart_1865909 baseEnd_1865909 := by
    simpa [prefixWord, tailWord_1865909, baseEnd_1865909] using wordTrace_append hprefix tailTrace_1865909
  have hstable : (prefixWord ++ tailWord_1865909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865909).length < 2 ^ (prefixWord ++ tailWord_1865909).sum := by decide
  have hdescent : baseEnd_1865909 < baseStart_1865909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865942 : List Nat := [5, 2, 1, 2, 1, 1, 1, 1, 2, 7]
def baseStart_1865942 : Nat := 118140960795 + 1865942 * 2 ^ 59
def prefixEnd_1865942 : Nat := 4983230072969 + 3 ^ 40 * 1865942 * 2
def baseEnd_1865942 : Nat := 319375039803947909014565

theorem tailTrace_1865942 : CollatzResearch.WordTrace tailWord_1865942 prefixEnd_1865942 319375039803947909014565 := by
  unfold tailWord_1865942
  simp only [CollatzResearch.WordTrace]
  refine ⟨4253530987876142897968505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45370997204012190911664053 4253530987876142897968505)
  ·
    refine ⟨3190148240907107173476379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4253530987876142897968505 3190148240907107173476379)
    ·
      refine ⟨4785222361360660760214569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3190148240907107173476379 4785222361360660760214569)
      ·
        refine ⟨3588916771020495570160927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4785222361360660760214569 3588916771020495570160927)
        ·
          refine ⟨5383375156530743355241391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3588916771020495570160927 5383375156530743355241391)
          ·
            refine ⟨8075062734796115032862087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5383375156530743355241391 8075062734796115032862087)
            ·
              refine ⟨12112594102194172549293131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8075062734796115032862087 12112594102194172549293131)
              ·
                refine ⟨18168891153291258823939697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12112594102194172549293131 18168891153291258823939697)
                ·
                  refine ⟨13626668364968444117954773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18168891153291258823939697 13626668364968444117954773)
                  ·
                    refine ⟨319375039803947909014565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13626668364968444117954773 319375039803947909014565)
                    ·
                      rfl

theorem cell23_1865942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_1865942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1865942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1865942 prefixEnd_1865942 := by exact prefixLift 1865942
  have htrace : WordTrace (prefixWord ++ tailWord_1865942) baseStart_1865942 baseEnd_1865942 := by
    simpa [prefixWord, tailWord_1865942, baseEnd_1865942] using wordTrace_append hprefix tailTrace_1865942
  have hstable : (prefixWord ++ tailWord_1865942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865942).length < 2 ^ (prefixWord ++ tailWord_1865942).sum := by decide
  have hdescent : baseEnd_1865942 < baseStart_1865942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865949 : List Nat := [1, 4, 3, 2, 1, 1, 1, 2, 3, 3, 2]
def baseStart_1865949 : Nat := 118140960795 + 1865949 * 2 ^ 59
def prefixEnd_1865949 : Nat := 4983230072969 + 3 ^ 40 * 1865949 * 2
def baseEnd_1865949 : Nat := 958128713776425199656163

theorem tailTrace_1865949 : CollatzResearch.WordTrace tailWord_1865949 prefixEnd_1865949 958128713776425199656163 := by
  unfold tailWord_1865949
  simp only [CollatzResearch.WordTrace]
  refine ⟨68056751116992926563000901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45371167411328617708667267 68056751116992926563000901)
  ·
    refine ⟨12760640834436173730562669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68056751116992926563000901 12760640834436173730562669)
    ·
      refine ⟨4785240312913565148961001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12760640834436173730562669 4785240312913565148961001)
      ·
        refine ⟨3588930234685173861720751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4785240312913565148961001 3588930234685173861720751)
        ·
          refine ⟨5383395352027760792581127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3588930234685173861720751 5383395352027760792581127)
          ·
            refine ⟨8075093028041641188871691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5383395352027760792581127 8075093028041641188871691)
            ·
              refine ⟨12112639542062461783307537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8075093028041641188871691 12112639542062461783307537)
              ·
                refine ⟨9084479656546846337480653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12112639542062461783307537 9084479656546846337480653)
                ·
                  refine ⟨3406679871205067376555245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9084479656546846337480653 3406679871205067376555245)
                  ·
                    refine ⟨1277504951701900266208217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3406679871205067376555245 1277504951701900266208217)
                    ·
                      refine ⟨958128713776425199656163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1277504951701900266208217 958128713776425199656163)
                      ·
                        rfl

theorem cell23_1865949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_1865949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1865949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1865949 prefixEnd_1865949 := by exact prefixLift 1865949
  have htrace : WordTrace (prefixWord ++ tailWord_1865949) baseStart_1865949 baseEnd_1865949 := by
    simpa [prefixWord, tailWord_1865949, baseEnd_1865949] using wordTrace_append hprefix tailTrace_1865949
  have hstable : (prefixWord ++ tailWord_1865949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865949).length < 2 ^ (prefixWord ++ tailWord_1865949).sum := by decide
  have hdescent : baseEnd_1865949 < baseStart_1865949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865995 : List Nat := [1, 1, 1, 1, 5, 2, 1, 1, 4, 3, 3]
def baseStart_1865995 : Nat := 118140960795 + 1865995 * 2 ^ 59
def prefixEnd_1865995 : Nat := 4983230072969 + 3 ^ 40 * 1865995 * 2
def baseEnd_1865995 : Nat := 958152333886532019680951

theorem tailTrace_1865995 : CollatzResearch.WordTrace tailWord_1865995 prefixEnd_1865995 958152333886532019680951 := by
  unfold tailWord_1865995
  simp only [CollatzResearch.WordTrace]
  refine ⟨68058428874826276419175439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45372285916550850946116959 68058428874826276419175439)
  ·
    refine ⟨102087643312239414628763159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68058428874826276419175439 102087643312239414628763159)
    ·
      refine ⟨153131464968359121943144739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102087643312239414628763159 153131464968359121943144739)
      ·
        refine ⟨229697197452538682914717109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153131464968359121943144739 229697197452538682914717109)
        ·
          refine ⟨21534112261175501523254729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 229697197452538682914717109 21534112261175501523254729)
          ·
            refine ⟨16150584195881626142441047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21534112261175501523254729 16150584195881626142441047)
            ·
              refine ⟨24225876293822439213661571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16150584195881626142441047 24225876293822439213661571)
              ·
                refine ⟨36338814440733658820492357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24225876293822439213661571 36338814440733658820492357)
                ·
                  refine ⟨6813527707637561028842317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36338814440733658820492357 6813527707637561028842317)
                  ·
                    refine ⟨2555072890364085385815869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6813527707637561028842317 2555072890364085385815869)
                    ·
                      refine ⟨958152333886532019680951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2555072890364085385815869 958152333886532019680951)
                      ·
                        rfl

theorem cell23_1865995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 4, 3, 3].length) (baseStart_1865995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1865995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1865995 prefixEnd_1865995 := by exact prefixLift 1865995
  have htrace : WordTrace (prefixWord ++ tailWord_1865995) baseStart_1865995 baseEnd_1865995 := by
    simpa [prefixWord, tailWord_1865995, baseEnd_1865995] using wordTrace_append hprefix tailTrace_1865995
  have hstable : (prefixWord ++ tailWord_1865995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865995).length < 2 ^ (prefixWord ++ tailWord_1865995).sum := by decide
  have hdescent : baseEnd_1865995 < baseStart_1865995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866013 : List Nat := [1, 4, 2, 3, 3, 1, 1, 1, 1, 4, 2]
def baseStart_1866013 : Nat := 118140960795 + 1866013 * 2 ^ 59
def prefixEnd_1866013 : Nat := 4983230072969 + 3 ^ 40 * 1866013 * 2
def baseEnd_1866013 : Nat := 958161576538312949255869

theorem tailTrace_1866013 : CollatzResearch.WordTrace tailWord_1866013 prefixEnd_1866013 958161576538312949255869 := by
  unfold tailWord_1866013
  simp only [CollatzResearch.WordTrace]
  refine ⟨68059085388761065493330693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45372723592507376995553795 68059085388761065493330693)
  ·
    refine ⟨12761078510392699779999505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68059085388761065493330693 12761078510392699779999505)
    ·
      refine ⟨9570808882794524834999629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12761078510392699779999505 9570808882794524834999629)
      ·
        refine ⟨3589053331047946813124861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9570808882794524834999629 3589053331047946813124861)
        ·
          refine ⟨1345894999142980054921823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3589053331047946813124861 1345894999142980054921823)
          ·
            refine ⟨2018842498714470082382735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1345894999142980054921823 2018842498714470082382735)
            ·
              refine ⟨3028263748071705123574103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2018842498714470082382735 3028263748071705123574103)
              ·
                refine ⟨4542395622107557685361155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3028263748071705123574103 4542395622107557685361155)
                ·
                  refine ⟨6813593433161336528041733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4542395622107557685361155 6813593433161336528041733)
                  ·
                    refine ⟨1277548768717750599007825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6813593433161336528041733 1277548768717750599007825)
                    ·
                      refine ⟨958161576538312949255869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1277548768717750599007825 958161576538312949255869)
                      ·
                        rfl

theorem cell23_1866013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_1866013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1866013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1866013 prefixEnd_1866013 := by exact prefixLift 1866013
  have htrace : WordTrace (prefixWord ++ tailWord_1866013) baseStart_1866013 baseEnd_1866013 := by
    simpa [prefixWord, tailWord_1866013, baseEnd_1866013] using wordTrace_append hprefix tailTrace_1866013
  have hstable : (prefixWord ++ tailWord_1866013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866013).length < 2 ^ (prefixWord ++ tailWord_1866013).sum := by decide
  have hdescent : baseEnd_1866013 < baseStart_1866013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866015 : List Nat := [1, 1, 2, 4, 3, 1, 1, 2, 1, 7]
def baseStart_1866015 : Nat := 118140960795 + 1866015 * 2 ^ 59
def prefixEnd_1866015 : Nat := 4983230072969 + 3 ^ 40 * 1866015 * 2
def baseEnd_1866015 : Nat := 319387534499873980476953

theorem tailTrace_1866015 : CollatzResearch.WordTrace tailWord_1866015 prefixEnd_1866015 319387534499873980476953 := by
  unfold tailWord_1866015
  simp only [CollatzResearch.WordTrace]
  refine ⟨68059158334753819834903499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45372772223169213223268999 68059158334753819834903499)
  ·
    refine ⟨102088737502130729752355249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68059158334753819834903499 102088737502130729752355249)
    ·
      refine ⟨76566553126598047314266437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102088737502130729752355249 76566553126598047314266437)
      ·
        refine ⟨14356228711237133871424957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76566553126598047314266437 14356228711237133871424957)
        ·
          refine ⟨5383585766713925201784359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14356228711237133871424957 5383585766713925201784359)
          ·
            refine ⟨8075378650070887802676539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5383585766713925201784359 8075378650070887802676539)
            ·
              refine ⟨12113067975106331704014809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8075378650070887802676539 12113067975106331704014809)
              ·
                refine ⟨9084800981329748778011107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12113067975106331704014809 9084800981329748778011107)
                ·
                  refine ⟨13627201471994623167016661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9084800981329748778011107 13627201471994623167016661)
                  ·
                    refine ⟨319387534499873980476953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13627201471994623167016661 319387534499873980476953)
                    ·
                      rfl

theorem cell23_1866015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 7].length) (baseStart_1866015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1866015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1866015 prefixEnd_1866015 := by exact prefixLift 1866015
  have htrace : WordTrace (prefixWord ++ tailWord_1866015) baseStart_1866015 baseEnd_1866015 := by
    simpa [prefixWord, tailWord_1866015, baseEnd_1866015] using wordTrace_append hprefix tailTrace_1866015
  have hstable : (prefixWord ++ tailWord_1866015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866015).length < 2 ^ (prefixWord ++ tailWord_1866015).sum := by decide
  have hdescent : baseEnd_1866015 < baseStart_1866015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866035 : List Nat := [1, 1, 1, 2, 5, 1, 1, 3, 1, 3, 4]
def baseStart_1866035 : Nat := 118140960795 + 1866035 * 2 ^ 59
def prefixEnd_1866035 : Nat := 4983230072969 + 3 ^ 40 * 1866035 * 2
def baseEnd_1866035 : Nat := 958172873112711863180767

theorem tailTrace_1866035 : CollatzResearch.WordTrace tailWord_1866035 prefixEnd_1866035 958172873112711863180767 := by
  unfold tailWord_1866035
  simp only [CollatzResearch.WordTrace]
  refine ⟨68059887794681363250631559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45373258529787575500421039 68059887794681363250631559)
  ·
    refine ⟨102089831692022044875947339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68059887794681363250631559 102089831692022044875947339)
    ·
      refine ⟨153134747538033067313921009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102089831692022044875947339 153134747538033067313921009)
      ·
        refine ⟨114851060653524800485440757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153134747538033067313921009 114851060653524800485440757)
        ·
          refine ⟨10767286936267950045510071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 114851060653524800485440757 10767286936267950045510071)
          ·
            refine ⟨16150930404401925068265107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10767286936267950045510071 16150930404401925068265107)
            ·
              refine ⟨24226395606602887602397661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16150930404401925068265107 24226395606602887602397661)
              ·
                refine ⟨9084898352476082850899123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24226395606602887602397661 9084898352476082850899123)
                ·
                  refine ⟨13627347528714124276348685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9084898352476082850899123 13627347528714124276348685)
                  ·
                    refine ⟨5110255323267796603630757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13627347528714124276348685 5110255323267796603630757)
                    ·
                      refine ⟨958172873112711863180767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5110255323267796603630757 958172873112711863180767)
                      ·
                        rfl

theorem cell23_1866035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 3, 4].length) (baseStart_1866035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1866035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1866035 prefixEnd_1866035 := by exact prefixLift 1866035
  have htrace : WordTrace (prefixWord ++ tailWord_1866035) baseStart_1866035 baseEnd_1866035 := by
    simpa [prefixWord, tailWord_1866035, baseEnd_1866035] using wordTrace_append hprefix tailTrace_1866035
  have hstable : (prefixWord ++ tailWord_1866035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866035).length < 2 ^ (prefixWord ++ tailWord_1866035).sum := by decide
  have hdescent : baseEnd_1866035 < baseStart_1866035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866036 : List Nat := [2, 5, 1, 1, 1, 4, 1, 3, 5]
def baseStart_1866036 : Nat := 118140960795 + 1866036 * 2 ^ 59
def prefixEnd_1866036 : Nat := 4983230072969 + 3 ^ 40 * 1866036 * 2
def baseEnd_1866036 : Nat := 106463709621485151029807

theorem tailTrace_1866036 : CollatzResearch.WordTrace tailWord_1866036 prefixEnd_1866036 106463709621485151029807 := by
  unfold tailWord_1866036
  simp only [CollatzResearch.WordTrace]
  refine ⟨34029962133838870210708981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45373282845118493614278641 34029962133838870210708981)
  ·
    refine ⟨3190308950047394082253967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34029962133838870210708981 3190308950047394082253967)
    ·
      refine ⟨4785463425071091123380951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3190308950047394082253967 4785463425071091123380951)
      ·
        refine ⟨7178195137606636685071427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4785463425071091123380951 7178195137606636685071427)
        ·
          refine ⟨10767292706409955027607141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7178195137606636685071427 10767292706409955027607141)
          ·
            refine ⟨2018867382451866567676339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10767292706409955027607141 2018867382451866567676339)
            ·
              refine ⟨3028301073677799851514509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2018867382451866567676339 3028301073677799851514509)
              ·
                refine ⟨1135612902629174944317941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3028301073677799851514509 1135612902629174944317941)
                ·
                  refine ⟨106463709621485151029807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1135612902629174944317941 106463709621485151029807)
                  ·
                    rfl

theorem cell23_1866036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_1866036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1866036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1866036 prefixEnd_1866036 := by exact prefixLift 1866036
  have htrace : WordTrace (prefixWord ++ tailWord_1866036) baseStart_1866036 baseEnd_1866036 := by
    simpa [prefixWord, tailWord_1866036, baseEnd_1866036] using wordTrace_append hprefix tailTrace_1866036
  have hstable : (prefixWord ++ tailWord_1866036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866036).length < 2 ^ (prefixWord ++ tailWord_1866036).sum := by decide
  have hdescent : baseEnd_1866036 < baseStart_1866036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866049 : List Nat := [1, 2, 5, 2, 2, 1, 1, 2, 2, 5]
def baseStart_1866049 : Nat := 118140960795 + 1866049 * 2 ^ 59
def prefixEnd_1866049 : Nat := 4983230072969 + 3 ^ 40 * 1866049 * 2
def baseEnd_1866049 : Nat := 319393353947291602801901

theorem tailTrace_1866049 : CollatzResearch.WordTrace tailWord_1866049 prefixEnd_1866049 319393353947291602801901 := by
  unfold tailWord_1866049
  simp only [CollatzResearch.WordTrace]
  refine ⟨68060398416630643641641201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45373598944420429094427467 68060398416630643641641201)
  ·
    refine ⟨51045298812472982731230901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68060398416630643641641201 51045298812472982731230901)
    ·
      refine ⟨4785496763669342131052897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51045298812472982731230901 4785496763669342131052897)
      ·
        refine ⟨3589122572752006598289673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4785496763669342131052897 3589122572752006598289673)
        ·
          refine ⟨2691841929564004948717255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3589122572752006598289673 2691841929564004948717255)
          ·
            refine ⟨4037762894346007423075883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2691841929564004948717255 4037762894346007423075883)
            ·
              refine ⟨6056644341519011134613825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4037762894346007423075883 6056644341519011134613825)
              ·
                refine ⟨4542483256139258350960369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6056644341519011134613825 4542483256139258350960369)
                ·
                  refine ⟨3406862442104443763220277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4542483256139258350960369 3406862442104443763220277)
                  ·
                    refine ⟨319393353947291602801901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3406862442104443763220277 319393353947291602801901)
                    ·
                      rfl

theorem cell23_1866049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_1866049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1866049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1866049 prefixEnd_1866049 := by exact prefixLift 1866049
  have htrace : WordTrace (prefixWord ++ tailWord_1866049) baseStart_1866049 baseEnd_1866049 := by
    simpa [prefixWord, tailWord_1866049, baseEnd_1866049] using wordTrace_append hprefix tailTrace_1866049
  have hstable : (prefixWord ++ tailWord_1866049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866049).length < 2 ^ (prefixWord ++ tailWord_1866049).sum := by decide
  have hdescent : baseEnd_1866049 < baseStart_1866049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866062 : List Nat := [4, 1, 1, 1, 1, 1, 2, 5, 3, 4]
def baseStart_1866062 : Nat := 118140960795 + 1866062 * 2 ^ 59
def prefixEnd_1866062 : Nat := 4983230072969 + 3 ^ 40 * 1866062 * 2
def baseEnd_1866062 : Nat := 319395579030127752514381

theorem tailTrace_1866062 : CollatzResearch.WordTrace tailWord_1866062 prefixEnd_1866062 319395579030127752514381 := by
  unfold tailWord_1866062
  simp only [CollatzResearch.WordTrace]
  refine ⟨8507609070697943357733055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45373915043722364574576293 8507609070697943357733055)
  ·
    refine ⟨12761413606046915036599583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8507609070697943357733055 12761413606046915036599583)
    ·
      refine ⟨19142120409070372554899375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12761413606046915036599583 19142120409070372554899375)
      ·
        refine ⟨28713180613605558832349063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19142120409070372554899375 28713180613605558832349063)
        ·
          refine ⟨43069770920408338248523595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28713180613605558832349063 43069770920408338248523595)
          ·
            refine ⟨64604656380612507372785393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43069770920408338248523595 64604656380612507372785393)
            ·
              refine ⟨48453492285459380529589045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64604656380612507372785393 48453492285459380529589045)
              ·
                refine ⟨4542514901761816924648973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48453492285459380529589045 4542514901761816924648973)
                ·
                  refine ⟨1703443088160681346743365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4542514901761816924648973 1703443088160681346743365)
                  ·
                    refine ⟨319395579030127752514381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1703443088160681346743365 319395579030127752514381)
                    ·
                      rfl

theorem cell23_1866062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 5, 3, 4].length) (baseStart_1866062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1866062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1866062 prefixEnd_1866062 := by exact prefixLift 1866062
  have htrace : WordTrace (prefixWord ++ tailWord_1866062) baseStart_1866062 baseEnd_1866062 := by
    simpa [prefixWord, tailWord_1866062, baseEnd_1866062] using wordTrace_append hprefix tailTrace_1866062
  have hstable : (prefixWord ++ tailWord_1866062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866062).length < 2 ^ (prefixWord ++ tailWord_1866062).sum := by decide
  have hdescent : baseEnd_1866062 < baseStart_1866062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866112 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 5, 5, 2]
def baseStart_1866112 : Nat := 118140960795 + 1866112 * 2 ^ 59
def prefixEnd_1866112 : Nat := 4983230072969 + 3 ^ 40 * 1866112 * 2
def baseEnd_1866112 : Nat := 958212411123108061917913

theorem tailTrace_1866112 : CollatzResearch.WordTrace tailWord_1866112 prefixEnd_1866112 958212411123108061917913 := by
  unfold tailWord_1866112
  simp only [CollatzResearch.WordTrace]
  refine ⟨34031348107701202700592295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45375130810268270267456393 34031348107701202700592295)
  ·
    refine ⟨51047022161551804050888443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34031348107701202700592295 51047022161551804050888443)
    ·
      refine ⟨76570533242327706076332665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51047022161551804050888443 76570533242327706076332665)
      ·
        refine ⟨57427899931745779557249499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76570533242327706076332665 57427899931745779557249499)
        ·
          refine ⟨86141849897618669335874249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57427899931745779557249499 86141849897618669335874249)
          ·
            refine ⟨64606387423214002001905687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86141849897618669335874249 64606387423214002001905687)
            ·
              refine ⟨96909581134821003002858531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64606387423214002001905687 96909581134821003002858531)
              ·
                refine ⟨145364371702231504504287797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96909581134821003002858531 145364371702231504504287797)
                ·
                  refine ⟨13627909847084203547276981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 145364371702231504504287797 13627909847084203547276981)
                  ·
                    refine ⟨1277616548164144082557217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13627909847084203547276981 1277616548164144082557217)
                    ·
                      refine ⟨958212411123108061917913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1277616548164144082557217 958212411123108061917913)
                      ·
                        rfl

theorem cell23_1866112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 5, 5, 2].length) (baseStart_1866112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1866112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1866112 prefixEnd_1866112 := by exact prefixLift 1866112
  have htrace : WordTrace (prefixWord ++ tailWord_1866112) baseStart_1866112 baseEnd_1866112 := by
    simpa [prefixWord, tailWord_1866112, baseEnd_1866112] using wordTrace_append hprefix tailTrace_1866112
  have hstable : (prefixWord ++ tailWord_1866112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866112).length < 2 ^ (prefixWord ++ tailWord_1866112).sum := by decide
  have hdescent : baseEnd_1866112 < baseStart_1866112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866113 : List Nat := [1, 2, 4, 3, 1, 1, 4, 2, 1, 4]
def baseStart_1866113 : Nat := 118140960795 + 1866113 * 2 ^ 59
def prefixEnd_1866113 : Nat := 4983230072969 + 3 ^ 40 * 1866113 * 2
def baseEnd_1866113 : Nat := 319404308201254186001803

theorem tailTrace_1866113 : CollatzResearch.WordTrace tailWord_1866113 prefixEnd_1866113 319404308201254186001803 := by
  unfold tailWord_1866113
  simp only [CollatzResearch.WordTrace]
  refine ⟨68062732688398782571970993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45375155125599188381313995 68062732688398782571970993)
  ·
    refine ⟨51047049516299086928978245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68062732688398782571970993 51047049516299086928978245)
    ·
      refine ⟨9571321784306078799183421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51047049516299086928978245 9571321784306078799183421)
      ·
        refine ⟨3589245669114779549693783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9571321784306078799183421 3589245669114779549693783)
        ·
          refine ⟨5383868503672169324540675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3589245669114779549693783 5383868503672169324540675)
          ·
            refine ⟨8075802755508253986811013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5383868503672169324540675 8075802755508253986811013)
            ·
              refine ⟨1514213016657797622527065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8075802755508253986811013 1514213016657797622527065)
              ·
                refine ⟨1135659762493348216895299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1514213016657797622527065 1135659762493348216895299)
                ·
                  refine ⟨1703489643740022325342949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1135659762493348216895299 1703489643740022325342949)
                  ·
                    refine ⟨319404308201254186001803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1703489643740022325342949 319404308201254186001803)
                    ·
                      rfl

theorem cell23_1866113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4, 2, 1, 4].length) (baseStart_1866113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1866113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1866113 prefixEnd_1866113 := by exact prefixLift 1866113
  have htrace : WordTrace (prefixWord ++ tailWord_1866113) baseStart_1866113 baseEnd_1866113 := by
    simpa [prefixWord, tailWord_1866113, baseEnd_1866113] using wordTrace_append hprefix tailTrace_1866113
  have hstable : (prefixWord ++ tailWord_1866113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866113).length < 2 ^ (prefixWord ++ tailWord_1866113).sum := by decide
  have hdescent : baseEnd_1866113 < baseStart_1866113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866119 : List Nat := [1, 1, 4, 2, 2, 1, 2, 3, 3, 1, 3]
def baseStart_1866119 : Nat := 118140960795 + 1866119 * 2 ^ 59
def prefixEnd_1866119 : Nat := 4983230072969 + 3 ^ 40 * 1866119 * 2
def baseEnd_1866119 : Nat := 958216005487689534530381

theorem tailTrace_1866119 : CollatzResearch.WordTrace tailWord_1866119 prefixEnd_1866119 958216005487689534530381 := by
  unfold tailWord_1866119
  simp only [CollatzResearch.WordTrace]
  refine ⟨68062951526377045596689411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45375301017584697064459607 68062951526377045596689411)
  ·
    refine ⟨102094427289565568395034117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68062951526377045596689411 102094427289565568395034117)
    ·
      refine ⟨19142705116793544074068897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102094427289565568395034117 19142705116793544074068897)
      ·
        refine ⟨14357028837595158055551673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19142705116793544074068897 14357028837595158055551673)
        ·
          refine ⟨10767771628196368541663755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14357028837595158055551673 10767771628196368541663755)
          ·
            refine ⟨16151657442294552812495633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10767771628196368541663755 16151657442294552812495633)
            ·
              refine ⟨12113743081720914609371725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16151657442294552812495633 12113743081720914609371725)
              ·
                refine ⟨4542653655645342978514397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12113743081720914609371725 4542653655645342978514397)
                ·
                  refine ⟨1703495120867003616942899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4542653655645342978514397 1703495120867003616942899)
                  ·
                    refine ⟨2555242681300505425414349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1703495120867003616942899 2555242681300505425414349)
                    ·
                      refine ⟨958216005487689534530381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2555242681300505425414349 958216005487689534530381)
                      ·
                        rfl

theorem cell23_1866119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 3, 3, 1, 3].length) (baseStart_1866119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1866119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1866119 prefixEnd_1866119 := by exact prefixLift 1866119
  have htrace : WordTrace (prefixWord ++ tailWord_1866119) baseStart_1866119 baseEnd_1866119 := by
    simpa [prefixWord, tailWord_1866119, baseEnd_1866119] using wordTrace_append hprefix tailTrace_1866119
  have hstable : (prefixWord ++ tailWord_1866119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866119).length < 2 ^ (prefixWord ++ tailWord_1866119).sum := by decide
  have hdescent : baseEnd_1866119 < baseStart_1866119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866136 : List Nat := [2, 1, 2, 5, 1, 2, 1, 2, 3, 1, 3]
def baseStart_1866136 : Nat := 118140960795 + 1866136 * 2 ^ 59
def prefixEnd_1866136 : Nat := 4983230072969 + 3 ^ 40 * 1866136 * 2
def baseEnd_1866136 : Nat := 958224734658815968017803

theorem tailTrace_1866136 : CollatzResearch.WordTrace tailWord_1866136 prefixEnd_1866136 958224734658815968017803 := by
  unfold tailWord_1866136
  simp only [CollatzResearch.WordTrace]
  refine ⟨34031785783657728750029131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45375714378210305000038841 34031785783657728750029131)
  ·
    refine ⟨51047678675486593125043697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34031785783657728750029131 51047678675486593125043697)
    ·
      refine ⟨38285759006614944843782773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51047678675486593125043697 38285759006614944843782773)
      ·
        refine ⟨3589289906870151079104635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38285759006614944843782773 3589289906870151079104635)
        ·
          refine ⟨5383934860305226618656953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3589289906870151079104635 5383934860305226618656953)
          ·
            refine ⟨4037951145228919963992715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5383934860305226618656953 4037951145228919963992715)
            ·
              refine ⟨6056926717843379945989073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4037951145228919963992715 6056926717843379945989073)
              ·
                refine ⟨4542695038382534959491805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6056926717843379945989073 4542695038382534959491805)
                ·
                  refine ⟨1703510639393450609809427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4542695038382534959491805 1703510639393450609809427)
                  ·
                    refine ⟨2555265959090175914714141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1703510639393450609809427 2555265959090175914714141)
                    ·
                      refine ⟨958224734658815968017803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2555265959090175914714141 958224734658815968017803)
                      ·
                        rfl

theorem cell23_1866136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_1866136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1866136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1866136 prefixEnd_1866136 := by exact prefixLift 1866136
  have htrace : WordTrace (prefixWord ++ tailWord_1866136) baseStart_1866136 baseEnd_1866136 := by
    simpa [prefixWord, tailWord_1866136, baseEnd_1866136] using wordTrace_append hprefix tailTrace_1866136
  have hstable : (prefixWord ++ tailWord_1866136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866136).length < 2 ^ (prefixWord ++ tailWord_1866136).sum := by decide
  have hdescent : baseEnd_1866136 < baseStart_1866136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866162 : List Nat := [3, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5]
def baseStart_1866162 : Nat := 118140960795 + 1866162 * 2 ^ 59
def prefixEnd_1866162 : Nat := 4983230072969 + 3 ^ 40 * 1866162 * 2
def baseEnd_1866162 : Nat := 958238085155832866292683

theorem tailTrace_1866162 : CollatzResearch.WordTrace tailWord_1866162 prefixEnd_1866162 958238085155832866292683 := by
  unfold tailWord_1866162
  simp only [CollatzResearch.WordTrace]
  refine ⟨17016129966305315985126185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45376346576814175960336493 17016129966305315985126185)
  ·
    refine ⟨12762097474728986988844639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17016129966305315985126185 12762097474728986988844639)
    ·
      refine ⟨19143146212093480483266959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12762097474728986988844639 19143146212093480483266959)
      ·
        refine ⟨28714719318140220724900439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19143146212093480483266959 28714719318140220724900439)
        ·
          refine ⟨43072078977210331087350659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28714719318140220724900439 43072078977210331087350659)
          ·
            refine ⟨64608118465815496631025989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43072078977210331087350659 64608118465815496631025989)
            ·
              refine ⟨12114022212340405618317373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64608118465815496631025989 12114022212340405618317373)
              ·
                refine ⟨4542758329627652106869015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12114022212340405618317373 4542758329627652106869015)
                ·
                  refine ⟨6814137494441478160303523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4542758329627652106869015 6814137494441478160303523)
                  ·
                    refine ⟨10221206241662217240455285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6814137494441478160303523 10221206241662217240455285)
                    ·
                      refine ⟨958238085155832866292683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10221206241662217240455285 958238085155832866292683)
                      ·
                        rfl

theorem cell23_1866162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5].length) (baseStart_1866162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1866162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1866162 prefixEnd_1866162 := by exact prefixLift 1866162
  have htrace : WordTrace (prefixWord ++ tailWord_1866162) baseStart_1866162 baseEnd_1866162 := by
    simpa [prefixWord, tailWord_1866162, baseEnd_1866162] using wordTrace_append hprefix tailTrace_1866162
  have hstable : (prefixWord ++ tailWord_1866162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866162).length < 2 ^ (prefixWord ++ tailWord_1866162).sum := by decide
  have hdescent : baseEnd_1866162 < baseStart_1866162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866169 : List Nat := [1, 2, 1, 4, 3, 2, 1, 1, 4, 4]
def baseStart_1866169 : Nat := 118140960795 + 1866169 * 2 ^ 59
def prefixEnd_1866169 : Nat := 4983230072969 + 3 ^ 40 * 1866169 * 2
def baseEnd_1866169 : Nat := 319413893173471446301717

theorem tailTrace_1866169 : CollatzResearch.WordTrace tailWord_1866169 prefixEnd_1866169 319413893173471446301717 := by
  unfold tailWord_1866169
  simp only [CollatzResearch.WordTrace]
  refine ⟨68064775176195904136009561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45376516784130602757339707 68064775176195904136009561)
  ·
    refine ⟨51048581382146928102007171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68064775176195904136009561 51048581382146928102007171)
    ·
      refine ⟨76572872073220392153010757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51048581382146928102007171 76572872073220392153010757)
      ·
        refine ⟨14357413513728823528689517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76572872073220392153010757 14357413513728823528689517)
        ·
          refine ⟨5384030067648308823258569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14357413513728823528689517 5384030067648308823258569)
          ·
            refine ⟨4038022550736231617443927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5384030067648308823258569 4038022550736231617443927)
            ·
              refine ⟨6057033826104347426165891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4038022550736231617443927 6057033826104347426165891)
              ·
                refine ⟨9085550739156521139248837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6057033826104347426165891 9085550739156521139248837)
                ·
                  refine ⟨1703540763591847713609157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9085550739156521139248837 1703540763591847713609157)
                  ·
                    refine ⟨319413893173471446301717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1703540763591847713609157 319413893173471446301717)
                    ·
                      rfl

theorem cell23_1866169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 4, 4].length) (baseStart_1866169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1866169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1866169 prefixEnd_1866169 := by exact prefixLift 1866169
  have htrace : WordTrace (prefixWord ++ tailWord_1866169) baseStart_1866169 baseEnd_1866169 := by
    simpa [prefixWord, tailWord_1866169, baseEnd_1866169] using wordTrace_append hprefix tailTrace_1866169
  have hstable : (prefixWord ++ tailWord_1866169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866169).length < 2 ^ (prefixWord ++ tailWord_1866169).sum := by decide
  have hdescent : baseEnd_1866169 < baseStart_1866169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866175 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 7]
def baseStart_1866175 : Nat := 118140960795 + 1866175 * 2 ^ 59
def prefixEnd_1866175 : Nat := 4983230072969 + 3 ^ 40 * 1866175 * 2
def baseEnd_1866175 : Nat := 958244760404341315430123

theorem tailTrace_1866175 : CollatzResearch.WordTrace tailWord_1866175 prefixEnd_1866175 958244760404341315430123 := by
  unfold tailWord_1866175
  simp only [CollatzResearch.WordTrace]
  refine ⟨68064994014174167160727979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45376662676116111440485319 68064994014174167160727979)
  ·
    refine ⟨102097491021261250741091969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68064994014174167160727979 102097491021261250741091969)
    ·
      refine ⟨76573118265945938055818977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102097491021261250741091969 76573118265945938055818977)
      ·
        refine ⟨57429838699459453541864233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76573118265945938055818977 57429838699459453541864233)
        ·
          refine ⟨43072379024594590156398175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57429838699459453541864233 43072379024594590156398175)
          ·
            refine ⟨64608568536891885234597263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43072379024594590156398175 64608568536891885234597263)
            ·
              refine ⟨96912852805337827851895895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64608568536891885234597263 96912852805337827851895895)
              ·
                refine ⟨145369279208006741777843843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96912852805337827851895895 145369279208006741777843843)
                ·
                  refine ⟨218053918812010112666765765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145369279208006741777843843 218053918812010112666765765)
                  ·
                    refine ⟨40885109777251896125018581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 218053918812010112666765765 40885109777251896125018581)
                    ·
                      refine ⟨958244760404341315430123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 40885109777251896125018581 958244760404341315430123)
                      ·
                        rfl

theorem cell23_1866175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 7].length) (baseStart_1866175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1866175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1866175 prefixEnd_1866175 := by exact prefixLift 1866175
  have htrace : WordTrace (prefixWord ++ tailWord_1866175) baseStart_1866175 baseEnd_1866175 := by
    simpa [prefixWord, tailWord_1866175, baseEnd_1866175] using wordTrace_append hprefix tailTrace_1866175
  have hstable : (prefixWord ++ tailWord_1866175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866175).length < 2 ^ (prefixWord ++ tailWord_1866175).sum := by decide
  have hdescent : baseEnd_1866175 < baseStart_1866175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866186 : List Nat := [3, 1, 2, 1, 2, 2, 5, 1, 2, 4]
def baseStart_1866186 : Nat := 118140960795 + 1866186 * 2 ^ 59
def prefixEnd_1866186 : Nat := 4983230072969 + 3 ^ 40 * 1866186 * 2
def baseEnd_1866186 : Nat := 319416802897180257464191

theorem tailTrace_1866186 : CollatzResearch.WordTrace tailWord_1866186 prefixEnd_1866186 319416802897180257464191 := by
  unfold tailWord_1866186
  simp only [CollatzResearch.WordTrace]
  refine ⟨17016348804283579009844603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45376930144756210692918941 17016348804283579009844603)
  ·
    refine ⟨25524523206425368514766905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17016348804283579009844603 25524523206425368514766905)
    ·
      refine ⟨19143392404819026386075179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25524523206425368514766905 19143392404819026386075179)
      ·
        refine ⟨28715088607228539579112769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19143392404819026386075179 28715088607228539579112769)
        ·
          refine ⟨21536316455421404684334577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28715088607228539579112769 21536316455421404684334577)
          ·
            refine ⟨16152237341566053513250933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21536316455421404684334577 16152237341566053513250933)
            ·
              refine ⟨1514272250771817516867275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16152237341566053513250933 1514272250771817516867275)
              ·
                refine ⟨2271408376157726275300913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1514272250771817516867275 2271408376157726275300913)
                ·
                  refine ⟨1703556282118294706475685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2271408376157726275300913 1703556282118294706475685)
                  ·
                    refine ⟨319416802897180257464191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1703556282118294706475685 319416802897180257464191)
                    ·
                      rfl

theorem cell23_1866186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5, 1, 2, 4].length) (baseStart_1866186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1866186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1866186 prefixEnd_1866186 := by exact prefixLift 1866186
  have htrace : WordTrace (prefixWord ++ tailWord_1866186) baseStart_1866186 baseEnd_1866186 := by
    simpa [prefixWord, tailWord_1866186, baseEnd_1866186] using wordTrace_append hprefix tailTrace_1866186
  have hstable : (prefixWord ++ tailWord_1866186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866186).length < 2 ^ (prefixWord ++ tailWord_1866186).sum := by decide
  have hdescent : baseEnd_1866186 < baseStart_1866186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866195 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 5, 9]
def baseStart_1866195 : Nat := 118140960795 + 1866195 * 2 ^ 59
def prefixEnd_1866195 : Nat := 4983230072969 + 3 ^ 40 * 1866195 * 2
def baseEnd_1866195 : Nat := 319418343339143745726677

theorem tailTrace_1866195 : CollatzResearch.WordTrace tailWord_1866195 prefixEnd_1866195 319418343339143745726677 := by
  unfold tailWord_1866195
  simp only [CollatzResearch.WordTrace]
  refine ⟨68065723474101710576456039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45377148982734473717637359 68065723474101710576456039)
  ·
    refine ⟨102098585211152565864684059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68065723474101710576456039 102098585211152565864684059)
    ·
      refine ⟨153147877816728848797026089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102098585211152565864684059 153147877816728848797026089)
      ·
        refine ⟨114860908362546636597769567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153147877816728848797026089 114860908362546636597769567)
        ·
          refine ⟨172291362543819954896654351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114860908362546636597769567 172291362543819954896654351)
          ·
            refine ⟨258437043815729932344981527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172291362543819954896654351 258437043815729932344981527)
            ·
              refine ⟨387655565723594898517472291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258437043815729932344981527 387655565723594898517472291)
              ·
                refine ⟨581483348585392347776208437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 387655565723594898517472291 581483348585392347776208437)
                ·
                  refine ⟨54514063929880532604019541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 581483348585392347776208437 54514063929880532604019541)
                  ·
                    refine ⟨319418343339143745726677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 54514063929880532604019541 319418343339143745726677)
                    ·
                      rfl

theorem cell23_1866195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 9].length) (baseStart_1866195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1866195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1866195 prefixEnd_1866195 := by exact prefixLift 1866195
  have htrace : WordTrace (prefixWord ++ tailWord_1866195) baseStart_1866195 baseEnd_1866195 := by
    simpa [prefixWord, tailWord_1866195, baseEnd_1866195] using wordTrace_append hprefix tailTrace_1866195
  have hstable : (prefixWord ++ tailWord_1866195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866195).length < 2 ^ (prefixWord ++ tailWord_1866195).sum := by decide
  have hdescent : baseEnd_1866195 < baseStart_1866195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866196 : List Nat := [2, 4, 1, 2, 2, 1, 1, 4, 1, 2, 3]
def baseStart_1866196 : Nat := 118140960795 + 1866196 * 2 ^ 59
def prefixEnd_1866196 : Nat := 4983230072969 + 3 ^ 40 * 1866196 * 2
def baseEnd_1866196 : Nat := 958255543498085733267527

theorem tailTrace_1866196 : CollatzResearch.WordTrace tailWord_1866196 prefixEnd_1866196 958255543498085733267527 := by
  unfold tailWord_1866196
  simp only [CollatzResearch.WordTrace]
  refine ⟨34032879973549043873621221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45377173298065391831494961 34032879973549043873621221)
  ·
    refine ⟨6381164995040445726303979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34032879973549043873621221 6381164995040445726303979)
    ·
      refine ⟨9571747492560668589455969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6381164995040445726303979 9571747492560668589455969)
      ·
        refine ⟨7178810619420501442091977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9571747492560668589455969 7178810619420501442091977)
        ·
          refine ⟨5384107964565376081568983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7178810619420501442091977 5384107964565376081568983)
          ·
            refine ⟨8076161946848064122353475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5384107964565376081568983 8076161946848064122353475)
            ·
              refine ⟨12114242920272096183530213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8076161946848064122353475 12114242920272096183530213)
              ·
                refine ⟨2271420547551018034411915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12114242920272096183530213 2271420547551018034411915)
                ·
                  refine ⟨3407130821326527051617873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2271420547551018034411915 3407130821326527051617873)
                  ·
                    refine ⟨2555348115994895288713405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3407130821326527051617873 2555348115994895288713405)
                    ·
                      refine ⟨958255543498085733267527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2555348115994895288713405 958255543498085733267527)
                      ·
                        rfl

theorem cell23_1866196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_1866196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1866196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1866196 prefixEnd_1866196 := by exact prefixLift 1866196
  have htrace : WordTrace (prefixWord ++ tailWord_1866196) baseStart_1866196 baseEnd_1866196 := by
    simpa [prefixWord, tailWord_1866196, baseEnd_1866196] using wordTrace_append hprefix tailTrace_1866196
  have hstable : (prefixWord ++ tailWord_1866196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866196).length < 2 ^ (prefixWord ++ tailWord_1866196).sum := by decide
  have hdescent : baseEnd_1866196 < baseStart_1866196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866209 : List Nat := [1, 2, 3, 1, 2, 2, 1, 1, 6, 1, 3]
def baseStart_1866209 : Nat := 118140960795 + 1866209 * 2 ^ 59
def prefixEnd_1866209 : Nat := 4983230072969 + 3 ^ 40 * 1866209 * 2
def baseEnd_1866209 : Nat := 958262218746594182404967

theorem tailTrace_1866209 : CollatzResearch.WordTrace tailWord_1866209 prefixEnd_1866209 958262218746594182404967 := by
  unfold tailWord_1866209
  simp only [CollatzResearch.WordTrace]
  refine ⟨68066234096050990967465681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45377489397367327311643787 68066234096050990967465681)
  ·
    refine ⟨51049675572038243225599261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68066234096050990967465681 51049675572038243225599261)
    ·
      refine ⟨19143628339514341209599723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51049675572038243225599261 19143628339514341209599723)
      ·
        refine ⟨28715442509271511814399585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19143628339514341209599723 28715442509271511814399585)
        ·
          refine ⟨21536581881953633860799689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28715442509271511814399585 21536581881953633860799689)
          ·
            refine ⟨16152436411465225395599767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21536581881953633860799689 16152436411465225395599767)
            ·
              refine ⟨24228654617197838093399651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16152436411465225395599767 24228654617197838093399651)
              ·
                refine ⟨36342981925796757140099477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24228654617197838093399651 36342981925796757140099477)
                ·
                  refine ⟨1703577277771722990942163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 36342981925796757140099477 1703577277771722990942163)
                  ·
                    refine ⟨2555365916657584486413245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1703577277771722990942163 2555365916657584486413245)
                    ·
                      refine ⟨958262218746594182404967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2555365916657584486413245 958262218746594182404967)
                      ·
                        rfl

theorem cell23_1866209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 6, 1, 3].length) (baseStart_1866209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1866209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1866209 prefixEnd_1866209 := by exact prefixLift 1866209
  have htrace : WordTrace (prefixWord ++ tailWord_1866209) baseStart_1866209 baseEnd_1866209 := by
    simpa [prefixWord, tailWord_1866209, baseEnd_1866209] using wordTrace_append hprefix tailTrace_1866209
  have hstable : (prefixWord ++ tailWord_1866209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866209).length < 2 ^ (prefixWord ++ tailWord_1866209).sum := by decide
  have hdescent : baseEnd_1866209 < baseStart_1866209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866232 : List Nat := [2, 1, 2, 1, 1, 4, 2, 1, 2, 3, 4]
def baseStart_1866232 : Nat := 118140960795 + 1866232 * 2 ^ 59
def prefixEnd_1866232 : Nat := 4983230072969 + 3 ^ 40 * 1866232 * 2
def baseEnd_1866232 : Nat := 958274028801647592417361

theorem tailTrace_1866232 : CollatzResearch.WordTrace tailWord_1866232 prefixEnd_1866232 958274028801647592417361 := by
  unfold tailWord_1866232
  simp only [CollatzResearch.WordTrace]
  refine ⟨34033536487483832947776475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45378048649978443930368633 34033536487483832947776475)
  ·
    refine ⟨51050304731225749421664713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34033536487483832947776475 51050304731225749421664713)
    ·
      refine ⟨38287728548419312066248535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51050304731225749421664713 38287728548419312066248535)
      ·
        refine ⟨57431592822628968099372803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38287728548419312066248535 57431592822628968099372803)
        ·
          refine ⟨86147389233943452149059205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57431592822628968099372803 86147389233943452149059205)
          ·
            refine ⟨16152635481364397277948601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86147389233943452149059205 16152635481364397277948601)
            ·
              refine ⟨12114476611023297958461451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16152635481364397277948601 12114476611023297958461451)
              ·
                refine ⟨18171714916534946937692177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12114476611023297958461451 18171714916534946937692177)
                ·
                  refine ⟨13628786187401210203269133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18171714916534946937692177 13628786187401210203269133)
                  ·
                    refine ⟨5110794820275453826225925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13628786187401210203269133 5110794820275453826225925)
                    ·
                      refine ⟨958274028801647592417361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5110794820275453826225925 958274028801647592417361)
                      ·
                        rfl

theorem cell23_1866232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 2, 3, 4].length) (baseStart_1866232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1866232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1866232 prefixEnd_1866232 := by exact prefixLift 1866232
  have htrace : WordTrace (prefixWord ++ tailWord_1866232) baseStart_1866232 baseEnd_1866232 := by
    simpa [prefixWord, tailWord_1866232, baseEnd_1866232] using wordTrace_append hprefix tailTrace_1866232
  have hstable : (prefixWord ++ tailWord_1866232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866232).length < 2 ^ (prefixWord ++ tailWord_1866232).sum := by decide
  have hdescent : baseEnd_1866232 < baseStart_1866232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866266 : List Nat := [3, 1, 1, 3, 1, 1, 2, 1, 6, 2, 2]
def baseStart_1866266 : Nat := 118140960795 + 1866266 * 2 ^ 59
def prefixEnd_1866266 : Nat := 4983230072969 + 3 ^ 40 * 1866266 * 2
def baseEnd_1866266 : Nat := 958291487143900459392205

theorem tailTrace_1866266 : CollatzResearch.WordTrace tailWord_1866266 prefixEnd_1866266 958291487143900459392205 := by
  unfold tailWord_1866266
  simp only [CollatzResearch.WordTrace]
  refine ⟨17017078264211122425572663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45378875371229659801527101 17017078264211122425572663)
  ·
    refine ⟨25525617396316683638358995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17017078264211122425572663 25525617396316683638358995)
    ·
      refine ⟨38288426094475025457538493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25525617396316683638358995 38288426094475025457538493)
      ·
        refine ⟨14358159785428134546576935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38288426094475025457538493 14358159785428134546576935)
        ·
          refine ⟨21537239678142201819865403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14358159785428134546576935 21537239678142201819865403)
          ·
            refine ⟨32305859517213302729798105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21537239678142201819865403 32305859517213302729798105)
            ·
              refine ⟨24229394637909977047348579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32305859517213302729798105 24229394637909977047348579)
              ·
                refine ⟨36344091956864965571022869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24229394637909977047348579 36344091956864965571022869)
                ·
                  refine ⟨1703629310478045261141697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 36344091956864965571022869 1703629310478045261141697)
                  ·
                    refine ⟨1277721982858533945856273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1703629310478045261141697 1277721982858533945856273)
                    ·
                      refine ⟨958291487143900459392205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1277721982858533945856273 958291487143900459392205)
                      ·
                        rfl

theorem cell23_1866266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 6, 2, 2].length) (baseStart_1866266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1866266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1866266 prefixEnd_1866266 := by exact prefixLift 1866266
  have htrace : WordTrace (prefixWord ++ tailWord_1866266) baseStart_1866266 baseEnd_1866266 := by
    simpa [prefixWord, tailWord_1866266, baseEnd_1866266] using wordTrace_append hprefix tailTrace_1866266
  have hstable : (prefixWord ++ tailWord_1866266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866266).length < 2 ^ (prefixWord ++ tailWord_1866266).sum := by decide
  have hdescent : baseEnd_1866266 < baseStart_1866266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866269 : List Nat := [1, 4, 2, 2, 1, 2, 2, 1, 2, 1, 5]
def baseStart_1866269 : Nat := 118140960795 + 1866269 * 2 ^ 59
def prefixEnd_1866269 : Nat := 4983230072969 + 3 ^ 40 * 1866269 * 2
def baseEnd_1866269 : Nat := 958293027585863947654691

theorem tailTrace_1866269 : CollatzResearch.WordTrace tailWord_1866269 prefixEnd_1866269 958293027585863947654691 := by
  unfold tailWord_1866269
  simp only [CollatzResearch.WordTrace]
  refine ⟨68068422475833621214649861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45378948317222414143099907 68068422475833621214649861)
  ·
    refine ⟨12762829214218803977746849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68068422475833621214649861 12762829214218803977746849)
    ·
      refine ⟨9572121910664102983310137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12762829214218803977746849 9572121910664102983310137)
      ·
        refine ⟨7179091432998077237482603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9572121910664102983310137 7179091432998077237482603)
        ·
          refine ⟨10768637149497115856223905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7179091432998077237482603 10768637149497115856223905)
          ·
            refine ⟨8076477862122836892167929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10768637149497115856223905 8076477862122836892167929)
            ·
              refine ⟨6057358396592127669125947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8076477862122836892167929 6057358396592127669125947)
              ·
                refine ⟨9086037594888191503688921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6057358396592127669125947 9086037594888191503688921)
                ·
                  refine ⟨6814528196166143627766691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9086037594888191503688921 6814528196166143627766691)
                  ·
                    refine ⟨10221792294249215441650037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6814528196166143627766691 10221792294249215441650037)
                    ·
                      refine ⟨958293027585863947654691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10221792294249215441650037 958293027585863947654691)
                      ·
                        rfl

theorem cell23_1866269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_1866269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1866269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1866269 prefixEnd_1866269 := by exact prefixLift 1866269
  have htrace : WordTrace (prefixWord ++ tailWord_1866269) baseStart_1866269 baseEnd_1866269 := by
    simpa [prefixWord, tailWord_1866269, baseEnd_1866269] using wordTrace_append hprefix tailTrace_1866269
  have hstable : (prefixWord ++ tailWord_1866269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866269).length < 2 ^ (prefixWord ++ tailWord_1866269).sum := by decide
  have hdescent : baseEnd_1866269 < baseStart_1866269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866312 : List Nat := [2, 1, 3, 1, 1, 1, 1, 4, 1, 1, 7]
def baseStart_1866312 : Nat := 118140960795 + 1866312 * 2 ^ 59
def prefixEnd_1866312 : Nat := 4983230072969 + 3 ^ 40 * 1866312 * 2
def baseEnd_1866312 : Nat := 958315107254007279416993

theorem tailTrace_1866312 : CollatzResearch.WordTrace tailWord_1866312 prefixEnd_1866312 958315107254007279416993 := by
  unfold tailWord_1866312
  simp only [CollatzResearch.WordTrace]
  refine ⟨34034995407338919779232595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45379993876451893038976793 34034995407338919779232595)
  ·
    refine ⟨51052493111008379668848893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34034995407338919779232595 51052493111008379668848893)
    ·
      refine ⟨19144684916628142375818335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51052493111008379668848893 19144684916628142375818335)
      ·
        refine ⟨28717027374942213563727503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19144684916628142375818335 28717027374942213563727503)
        ·
          refine ⟨43075541062413320345591255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28717027374942213563727503 43075541062413320345591255)
          ·
            refine ⟨64613311593619980518386883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43075541062413320345591255 64613311593619980518386883)
            ·
              refine ⟨96919967390429970777580325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64613311593619980518386883 96919967390429970777580325)
              ·
                refine ⟨18172493885705619520796311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96919967390429970777580325 18172493885705619520796311)
                ·
                  refine ⟨27258740828558429281194467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18172493885705619520796311 27258740828558429281194467)
                  ·
                    refine ⟨40888111242837643921791701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27258740828558429281194467 40888111242837643921791701)
                    ·
                      refine ⟨958315107254007279416993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 40888111242837643921791701 958315107254007279416993)
                      ·
                        rfl

theorem cell23_1866312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_1866312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1866312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1866312 prefixEnd_1866312 := by exact prefixLift 1866312
  have htrace : WordTrace (prefixWord ++ tailWord_1866312) baseStart_1866312 baseEnd_1866312 := by
    simpa [prefixWord, tailWord_1866312, baseEnd_1866312] using wordTrace_append hprefix tailTrace_1866312
  have hstable : (prefixWord ++ tailWord_1866312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866312).length < 2 ^ (prefixWord ++ tailWord_1866312).sum := by decide
  have hdescent : baseEnd_1866312 < baseStart_1866312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866319 : List Nat := [1, 1, 2, 1, 1, 2, 7, 1, 2, 5]
def baseStart_1866319 : Nat := 118140960795 + 1866319 * 2 ^ 59
def prefixEnd_1866319 : Nat := 4983230072969 + 3 ^ 40 * 1866319 * 2
def baseEnd_1866319 : Nat := 319439567206196250676487

theorem tailTrace_1866319 : CollatzResearch.WordTrace tailWord_1866319 prefixEnd_1866319 319439567206196250676487 := by
  unfold tailWord_1866319
  simp only [CollatzResearch.WordTrace]
  refine ⟨68070246125652479753970011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45380164083768319835980007 68070246125652479753970011)
  ·
    refine ⟨102105369188478719630955017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68070246125652479753970011 102105369188478719630955017)
    ·
      refine ⟨76579026891359039723216263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102105369188478719630955017 76579026891359039723216263)
      ·
        refine ⟨114868540337038559584824395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76579026891359039723216263 114868540337038559584824395)
        ·
          refine ⟨172302810505557839377236593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114868540337038559584824395 172302810505557839377236593)
          ·
            refine ⟨129227107879168379532927445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172302810505557839377236593 129227107879168379532927445)
            ·
              refine ⟨3028760340918008895302987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 129227107879168379532927445 3028760340918008895302987)
              ·
                refine ⟨4543140511377013342954481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3028760340918008895302987 4543140511377013342954481)
                ·
                  refine ⟨3407355383532760007215861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4543140511377013342954481 3407355383532760007215861)
                  ·
                    refine ⟨319439567206196250676487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3407355383532760007215861 319439567206196250676487)
                    ·
                      rfl

theorem cell23_1866319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 1, 2, 5].length) (baseStart_1866319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1866319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1866319 prefixEnd_1866319 := by exact prefixLift 1866319
  have htrace : WordTrace (prefixWord ++ tailWord_1866319) baseStart_1866319 baseEnd_1866319 := by
    simpa [prefixWord, tailWord_1866319, baseEnd_1866319] using wordTrace_append hprefix tailTrace_1866319
  have hstable : (prefixWord ++ tailWord_1866319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866319).length < 2 ^ (prefixWord ++ tailWord_1866319).sum := by decide
  have hdescent : baseEnd_1866319 < baseStart_1866319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866334 : List Nat := [4, 4, 1, 2, 1, 1, 1, 1, 4, 2, 2]
def baseStart_1866334 : Nat := 118140960795 + 1866334 * 2 ^ 59
def prefixEnd_1866334 : Nat := 4983230072969 + 3 ^ 40 * 1866334 * 2
def baseEnd_1866334 : Nat := 958326403828406193341893

theorem tailTrace_1866334 : CollatzResearch.WordTrace tailWord_1866334 prefixEnd_1866334 958326403828406193341893 := by
  unfold tailWord_1866334
  simp only [CollatzResearch.WordTrace]
  refine ⟨8508849152574767164470757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45380528813732091543844037 8508849152574767164470757)
  ·
    refine ⟨1595409216107768843338267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8508849152574767164470757 1595409216107768843338267)
    ·
      refine ⟨2393113824161653265007401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1595409216107768843338267 2393113824161653265007401)
      ·
        refine ⟨1794835368121239948755551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2393113824161653265007401 1794835368121239948755551)
        ·
          refine ⟨2692253052181859923133327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1794835368121239948755551 2692253052181859923133327)
          ·
            refine ⟨4038379578272789884699991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2692253052181859923133327 4038379578272789884699991)
            ·
              refine ⟨6057569367409184827049987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4038379578272789884699991 6057569367409184827049987)
              ·
                refine ⟨9086354051113777240574981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6057569367409184827049987 9086354051113777240574981)
                ·
                  refine ⟨1703691384583833232607809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9086354051113777240574981 1703691384583833232607809)
                  ·
                    refine ⟨1277768538437874924455857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1703691384583833232607809 1277768538437874924455857)
                    ·
                      refine ⟨958326403828406193341893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1277768538437874924455857 958326403828406193341893)
                      ·
                        rfl

theorem cell23_1866334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_1866334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1866334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1866334 prefixEnd_1866334 := by exact prefixLift 1866334
  have htrace : WordTrace (prefixWord ++ tailWord_1866334) baseStart_1866334 baseEnd_1866334 := by
    simpa [prefixWord, tailWord_1866334, baseEnd_1866334] using wordTrace_append hprefix tailTrace_1866334
  have hstable : (prefixWord ++ tailWord_1866334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866334).length < 2 ^ (prefixWord ++ tailWord_1866334).sum := by decide
  have hdescent : baseEnd_1866334 < baseStart_1866334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866339 : List Nat := [1, 1, 1, 5, 1, 2, 2, 1, 4, 1, 4]
def baseStart_1866339 : Nat := 118140960795 + 1866339 * 2 ^ 59
def prefixEnd_1866339 : Nat := 4983230072969 + 3 ^ 40 * 1866339 * 2
def baseEnd_1866339 : Nat := 958328971231678673779369

theorem tailTrace_1866339 : CollatzResearch.WordTrace tailWord_1866339 prefixEnd_1866339 958328971231678673779369 := by
  unfold tailWord_1866339
  simp only [CollatzResearch.WordTrace]
  refine ⟨68070975585580023169698071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45380650390386682113132047 68070975585580023169698071)
  ·
    refine ⟨102106463378370034754547107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68070975585580023169698071 102106463378370034754547107)
    ·
      refine ⟨153159695067555052131820661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102106463378370034754547107 153159695067555052131820661)
      ·
        refine ⟨14358721412583286137358187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 153159695067555052131820661 14358721412583286137358187)
        ·
          refine ⟨21538082118874929206037281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14358721412583286137358187 21538082118874929206037281)
          ·
            refine ⟨16153561589156196904527961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21538082118874929206037281 16153561589156196904527961)
            ·
              refine ⟨12115171191867147678395971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16153561589156196904527961 12115171191867147678395971)
              ·
                refine ⟨18172756787800721517593957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12115171191867147678395971 18172756787800721517593957)
                ·
                  refine ⟨3407391897712635284548867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18172756787800721517593957 3407391897712635284548867)
                  ·
                    refine ⟨5111087846568952926823301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3407391897712635284548867 5111087846568952926823301)
                    ·
                      refine ⟨958328971231678673779369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5111087846568952926823301 958328971231678673779369)
                      ·
                        rfl

theorem cell23_1866339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_1866339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1866339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1866339 prefixEnd_1866339 := by exact prefixLift 1866339
  have htrace : WordTrace (prefixWord ++ tailWord_1866339) baseStart_1866339 baseEnd_1866339 := by
    simpa [prefixWord, tailWord_1866339, baseEnd_1866339] using wordTrace_append hprefix tailTrace_1866339
  have hstable : (prefixWord ++ tailWord_1866339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866339).length < 2 ^ (prefixWord ++ tailWord_1866339).sum := by decide
  have hdescent : baseEnd_1866339 < baseStart_1866339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866359 : List Nat := [1, 1, 3, 1, 1, 3, 3, 2, 1, 4, 3]
def baseStart_1866359 : Nat := 118140960795 + 1866359 * 2 ^ 59
def prefixEnd_1866359 : Nat := 4983230072969 + 3 ^ 40 * 1866359 * 2
def baseEnd_1866359 : Nat := 958339240844768595529277

theorem tailTrace_1866359 : CollatzResearch.WordTrace tailWord_1866359 prefixEnd_1866359 958339240844768595529277 := by
  unfold tailWord_1866359
  simp only [CollatzResearch.WordTrace]
  refine ⟨68071705045507566585426131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45381136697005044390284087 68071705045507566585426131)
  ·
    refine ⟨102107557568261349878139197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68071705045507566585426131 102107557568261349878139197)
    ·
      refine ⟨38290334088098006204302199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102107557568261349878139197 38290334088098006204302199)
      ·
        refine ⟨57435501132147009306453299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38290334088098006204302199 57435501132147009306453299)
        ·
          refine ⟨86153251698220513959679949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57435501132147009306453299 86153251698220513959679949)
          ·
            refine ⟨32307469386832692734879981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86153251698220513959679949 32307469386832692734879981)
            ·
              refine ⟨12115301020062259775579993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32307469386832692734879981 12115301020062259775579993)
              ·
                refine ⟨9086475765046694831684995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12115301020062259775579993 9086475765046694831684995)
                ·
                  refine ⟨13629713647570042247527493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9086475765046694831684995 13629713647570042247527493)
                  ·
                    refine ⟨2555571308919382921411405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13629713647570042247527493 2555571308919382921411405)
                    ·
                      refine ⟨958339240844768595529277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2555571308919382921411405 958339240844768595529277)
                      ·
                        rfl

theorem cell23_1866359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 4, 3].length) (baseStart_1866359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1866359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1866359 prefixEnd_1866359 := by exact prefixLift 1866359
  have htrace : WordTrace (prefixWord ++ tailWord_1866359) baseStart_1866359 baseEnd_1866359 := by
    simpa [prefixWord, tailWord_1866359, baseEnd_1866359] using wordTrace_append hprefix tailTrace_1866359
  have hstable : (prefixWord ++ tailWord_1866359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866359).length < 2 ^ (prefixWord ++ tailWord_1866359).sum := by decide
  have hdescent : baseEnd_1866359 < baseStart_1866359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866369 : List Nat := [1, 2, 4, 2, 1, 1, 1, 1, 2, 4, 4]
def baseStart_1866369 : Nat := 118140960795 + 1866369 * 2 ^ 59
def prefixEnd_1866369 : Nat := 4983230072969 + 3 ^ 40 * 1866369 * 2
def baseEnd_1866369 : Nat := 958344375651313556404231

theorem tailTrace_1866369 : CollatzResearch.WordTrace tailWord_1866369 prefixEnd_1866369 958344375651313556404231 := by
  unfold tailWord_1866369
  simp only [CollatzResearch.WordTrace]
  refine ⟨68072069775471338293290161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45381379850314225528860107 68072069775471338293290161)
  ·
    refine ⟨51054052331603503719967621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68072069775471338293290161 51054052331603503719967621)
    ·
      refine ⟨9572634812175656947493929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51054052331603503719967621 9572634812175656947493929)
      ·
        refine ⟨7179476109131742710620447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9572634812175656947493929 7179476109131742710620447)
        ·
          refine ⟨10769214163697614065930671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7179476109131742710620447 10769214163697614065930671)
          ·
            refine ⟨16153821245546421098896007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10769214163697614065930671 16153821245546421098896007)
            ·
              refine ⟨24230731868319631648344011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16153821245546421098896007 24230731868319631648344011)
              ·
                refine ⟨36346097802479447472516017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24230731868319631648344011 36346097802479447472516017)
                ·
                  refine ⟨27259573351859585604387013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36346097802479447472516017 27259573351859585604387013)
                  ·
                    refine ⟨5111170003473672300822565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27259573351859585604387013 5111170003473672300822565)
                    ·
                      refine ⟨958344375651313556404231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5111170003473672300822565 958344375651313556404231)
                      ·
                        rfl

theorem cell23_1866369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_1866369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1866369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1866369 prefixEnd_1866369 := by exact prefixLift 1866369
  have htrace : WordTrace (prefixWord ++ tailWord_1866369) baseStart_1866369 baseEnd_1866369 := by
    simpa [prefixWord, tailWord_1866369, baseEnd_1866369] using wordTrace_append hprefix tailTrace_1866369
  have hstable : (prefixWord ++ tailWord_1866369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866369).length < 2 ^ (prefixWord ++ tailWord_1866369).sum := by decide
  have hdescent : baseEnd_1866369 < baseStart_1866369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866400 : List Nat := [2, 1, 1, 4, 5, 1, 1, 1, 3, 4]
def baseStart_1866400 : Nat := 118140960795 + 1866400 * 2 ^ 59
def prefixEnd_1866400 : Nat := 4983230072969 + 3 ^ 40 * 1866400 * 2
def baseEnd_1866400 : Nat := 319453431183867645038863

theorem tailTrace_1866400 : CollatzResearch.WordTrace tailWord_1866400 prefixEnd_1866400 319453431183867645038863 := by
  unfold tailWord_1866400
  simp only [CollatzResearch.WordTrace]
  refine ⟨34036600219179515293834327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45382133625572687058445769 34036600219179515293834327)
  ·
    refine ⟨51054900328769272940751491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34036600219179515293834327 51054900328769272940751491)
    ·
      refine ⟨76582350493153909411127237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51054900328769272940751491 76582350493153909411127237)
      ·
        refine ⟨14359190717466358014586357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76582350493153909411127237 14359190717466358014586357)
        ·
          refine ⟨1346174129762471063867471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14359190717466358014586357 1346174129762471063867471)
          ·
            refine ⟨2019261194643706595801207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1346174129762471063867471 2019261194643706595801207)
            ·
              refine ⟨3028891791965559893701811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2019261194643706595801207 3028891791965559893701811)
              ·
                refine ⟨4543337687948339840552717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3028891791965559893701811 4543337687948339840552717)
                ·
                  refine ⟨1703751632980627440207269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4543337687948339840552717 1703751632980627440207269)
                  ·
                    refine ⟨319453431183867645038863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1703751632980627440207269 319453431183867645038863)
                    ·
                      rfl

theorem cell23_1866400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 1, 3, 4].length) (baseStart_1866400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1866400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1866400 prefixEnd_1866400 := by exact prefixLift 1866400
  have htrace : WordTrace (prefixWord ++ tailWord_1866400) baseStart_1866400 baseEnd_1866400 := by
    simpa [prefixWord, tailWord_1866400, baseEnd_1866400] using wordTrace_append hprefix tailTrace_1866400
  have hstable : (prefixWord ++ tailWord_1866400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866400).length < 2 ^ (prefixWord ++ tailWord_1866400).sum := by decide
  have hdescent : baseEnd_1866400 < baseStart_1866400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866413 : List Nat := [1, 5, 2, 1, 1, 2, 4, 1, 6]
def baseStart_1866413 : Nat := 118140960795 + 1866413 * 2 ^ 59
def prefixEnd_1866413 : Nat := 4983230072969 + 3 ^ 40 * 1866413 * 2
def baseEnd_1866413 : Nat := 106485218755567931583781

theorem tailTrace_1866413 : CollatzResearch.WordTrace tailWord_1866413 prefixEnd_1866413 106485218755567931583781 := by
  unfold tailWord_1866413
  simp only [CollatzResearch.WordTrace]
  refine ⟨68073674587311933807891893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45382449724874622538594595 68073674587311933807891893)
  ·
    refine ⟨6381906992560493794489865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68073674587311933807891893 6381906992560493794489865)
    ·
      refine ⟨4786430244420370345867399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6381906992560493794489865 4786430244420370345867399)
      ·
        refine ⟨7179645366630555518801099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4786430244420370345867399 7179645366630555518801099)
        ·
          refine ⟨10769468049945833278201649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7179645366630555518801099 10769468049945833278201649)
          ·
            refine ⟨8077101037459374958651237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10769468049945833278201649 8077101037459374958651237)
            ·
              refine ⟨1514456444523632804747107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8077101037459374958651237 1514456444523632804747107)
              ·
                refine ⟨2271684666785449207120661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1514456444523632804747107 2271684666785449207120661)
                ·
                  refine ⟨106485218755567931583781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2271684666785449207120661 106485218755567931583781)
                  ·
                    rfl

theorem cell23_1866413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4, 1, 6].length) (baseStart_1866413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1866413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1866413 prefixEnd_1866413 := by exact prefixLift 1866413
  have htrace : WordTrace (prefixWord ++ tailWord_1866413) baseStart_1866413 baseEnd_1866413 := by
    simpa [prefixWord, tailWord_1866413, baseEnd_1866413] using wordTrace_append hprefix tailTrace_1866413
  have hstable : (prefixWord ++ tailWord_1866413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866413).length < 2 ^ (prefixWord ++ tailWord_1866413).sum := by decide
  have hdescent : baseEnd_1866413 < baseStart_1866413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866416 : List Nat := [2, 1, 1, 1, 2, 1, 3, 1, 6, 3, 2]
def baseStart_1866416 : Nat := 118140960795 + 1866416 * 2 ^ 59
def prefixEnd_1866416 : Nat := 4983230072969 + 3 ^ 40 * 1866416 * 2
def baseEnd_1866416 : Nat := 958368509242074872516515

theorem tailTrace_1866416 : CollatzResearch.WordTrace tailWord_1866416 prefixEnd_1866416 958368509242074872516515 := by
  unfold tailWord_1866416
  simp only [CollatzResearch.WordTrace]
  refine ⟨34036892003150532660125551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45382522670867376880167401 34036892003150532660125551)
  ·
    refine ⟨51055338004725798990188327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34036892003150532660125551 51055338004725798990188327)
    ·
      refine ⟨76583007007088698485282491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51055338004725798990188327 76583007007088698485282491)
      ·
        refine ⟨114874510510633047727923737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76583007007088698485282491 114874510510633047727923737)
        ·
          refine ⟨86155882882974785795942803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114874510510633047727923737 86155882882974785795942803)
          ·
            refine ⟨129233824324462178693914205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86155882882974785795942803 129233824324462178693914205)
            ·
              refine ⟨48462684121673317010217827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129233824324462178693914205 48462684121673317010217827)
              ·
                refine ⟨72694026182509975515326741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48462684121673317010217827 72694026182509975515326741)
                ·
                  refine ⟨3407532477305155102280941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 72694026182509975515326741 3407532477305155102280941)
                  ·
                    refine ⟨1277824678989433163355353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3407532477305155102280941 1277824678989433163355353)
                    ·
                      refine ⟨958368509242074872516515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1277824678989433163355353 958368509242074872516515)
                      ·
                        rfl

theorem cell23_1866416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 6, 3, 2].length) (baseStart_1866416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1866416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1866416 prefixEnd_1866416 := by exact prefixLift 1866416
  have htrace : WordTrace (prefixWord ++ tailWord_1866416) baseStart_1866416 baseEnd_1866416 := by
    simpa [prefixWord, tailWord_1866416, baseEnd_1866416] using wordTrace_append hprefix tailTrace_1866416
  have hstable : (prefixWord ++ tailWord_1866416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866416).length < 2 ^ (prefixWord ++ tailWord_1866416).sum := by decide
  have hdescent : baseEnd_1866416 < baseStart_1866416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866514 : List Nat := [3, 2, 4, 1, 2, 1, 2, 1, 3, 2, 2]
def baseStart_1866514 : Nat := 118140960795 + 1866514 * 2 ^ 59
def prefixEnd_1866514 : Nat := 4983230072969 + 3 ^ 40 * 1866514 * 2
def baseEnd_1866514 : Nat := 958418830346215489091065

theorem tailTrace_1866514 : CollatzResearch.WordTrace tailWord_1866514 prefixEnd_1866514 958418830346215489091065 := by
  unfold tailWord_1866514
  simp only [CollatzResearch.WordTrace]
  refine ⟨17019339589986507014329649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45384905573297352038212397 17019339589986507014329649)
  ·
    refine ⟨12764504692489880260747237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17019339589986507014329649 12764504692489880260747237)
    ·
      refine ⟨2393344629841852548890107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12764504692489880260747237 2393344629841852548890107)
      ·
        refine ⟨3590016944762778823335161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2393344629841852548890107 3590016944762778823335161)
        ·
          refine ⟨2692512708572084117501371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3590016944762778823335161 2692512708572084117501371)
          ·
            refine ⟨4038769062858126176252057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2692512708572084117501371 4038769062858126176252057)
            ·
              refine ⟨3029076797143594632189043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4038769062858126176252057 3029076797143594632189043)
              ·
                refine ⟨4543615195715391948283565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3029076797143594632189043 4543615195715391948283565)
                ·
                  refine ⟨1703855698393271980606337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4543615195715391948283565 1703855698393271980606337)
                  ·
                    refine ⟨1277891773794953985454753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1703855698393271980606337 1277891773794953985454753)
                    ·
                      refine ⟨958418830346215489091065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1277891773794953985454753 958418830346215489091065)
                      ·
                        rfl

theorem cell23_1866514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_1866514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1866514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1866514 prefixEnd_1866514 := by exact prefixLift 1866514
  have htrace : WordTrace (prefixWord ++ tailWord_1866514) baseStart_1866514 baseEnd_1866514 := by
    simpa [prefixWord, tailWord_1866514, baseEnd_1866514] using wordTrace_append hprefix tailTrace_1866514
  have hstable : (prefixWord ++ tailWord_1866514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866514).length < 2 ^ (prefixWord ++ tailWord_1866514).sum := by decide
  have hdescent : baseEnd_1866514 < baseStart_1866514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866530 : List Nat := [3, 3, 1, 1, 2, 4, 1, 1, 1, 3, 3]
def baseStart_1866530 : Nat := 118140960795 + 1866530 * 2 ^ 59
def prefixEnd_1866530 : Nat := 4983230072969 + 3 ^ 40 * 1866530 * 2
def baseEnd_1866530 : Nat := 958427046036687426490991

theorem tailTrace_1866530 : CollatzResearch.WordTrace tailWord_1866530 prefixEnd_1866530 958427046036687426490991 := by
  unfold tailWord_1866530
  simp only [CollatzResearch.WordTrace]
  refine ⟨17019485481972015697475261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45385294618592041859934029 17019485481972015697475261)
  ·
    refine ⟨6382307055739505886553223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17019485481972015697475261 6382307055739505886553223)
    ·
      refine ⟨9573460583609258829829835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6382307055739505886553223 9573460583609258829829835)
      ·
        refine ⟨14360190875413888244744753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9573460583609258829829835 14360190875413888244744753)
        ·
          refine ⟨10770143156560416183558565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14360190875413888244744753 10770143156560416183558565)
          ·
            refine ⟨2019401841855078034417231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10770143156560416183558565 2019401841855078034417231)
            ·
              refine ⟨3029102762782617051625847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2019401841855078034417231 3029102762782617051625847)
              ·
                refine ⟨4543654144173925577438771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3029102762782617051625847 4543654144173925577438771)
                ·
                  refine ⟨6815481216260888366158157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4543654144173925577438771 6815481216260888366158157)
                  ·
                    refine ⟨2555805456097833137309309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6815481216260888366158157 2555805456097833137309309)
                    ·
                      refine ⟨958427046036687426490991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2555805456097833137309309 958427046036687426490991)
                      ·
                        rfl

theorem cell23_1866530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 1, 1, 3, 3].length) (baseStart_1866530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1866530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1866530 prefixEnd_1866530 := by exact prefixLift 1866530
  have htrace : WordTrace (prefixWord ++ tailWord_1866530) baseStart_1866530 baseEnd_1866530 := by
    simpa [prefixWord, tailWord_1866530, baseEnd_1866530] using wordTrace_append hprefix tailTrace_1866530
  have hstable : (prefixWord ++ tailWord_1866530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866530).length < 2 ^ (prefixWord ++ tailWord_1866530).sum := by decide
  have hdescent : baseEnd_1866530 < baseStart_1866530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866540 : List Nat := [2, 2, 1, 1, 1, 4, 4, 2, 1, 3, 2]
def baseStart_1866540 : Nat := 118140960795 + 1866540 * 2 ^ 59
def prefixEnd_1866540 : Nat := 4983230072969 + 3 ^ 40 * 1866540 * 2
def baseEnd_1866540 : Nat := 958432180843232387365945

theorem tailTrace_1866540 : CollatzResearch.WordTrace tailWord_1866540 prefixEnd_1866540 958432180843232387365945 := by
  unfold tailWord_1866540
  simp only [CollatzResearch.WordTrace]
  refine ⟨34039153328925917248882537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45385537771901222998510049 34039153328925917248882537)
  ·
    refine ⟨25529364996694437936661903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34039153328925917248882537 25529364996694437936661903)
    ·
      refine ⟨38294047495041656904992855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25529364996694437936661903 38294047495041656904992855)
      ·
        refine ⟨57441071242562485357489283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38294047495041656904992855 57441071242562485357489283)
        ·
          refine ⟨86161606863843728036233925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57441071242562485357489283 86161606863843728036233925)
          ·
            refine ⟨16155301286970699006793861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86161606863843728036233925 16155301286970699006793861)
            ·
              refine ⟨3029118991307006063773849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16155301286970699006793861 3029118991307006063773849)
              ·
                refine ⟨2271839243480254547830387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3029118991307006063773849 2271839243480254547830387)
                ·
                  refine ⟨3407758865220381821745581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2271839243480254547830387 3407758865220381821745581)
                  ·
                    refine ⟨1277909574457643183154593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3407758865220381821745581 1277909574457643183154593)
                    ·
                      refine ⟨958432180843232387365945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1277909574457643183154593 958432180843232387365945)
                      ·
                        rfl

theorem cell23_1866540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 3, 2].length) (baseStart_1866540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1866540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1866540 prefixEnd_1866540 := by exact prefixLift 1866540
  have htrace : WordTrace (prefixWord ++ tailWord_1866540) baseStart_1866540 baseEnd_1866540 := by
    simpa [prefixWord, tailWord_1866540, baseEnd_1866540] using wordTrace_append hprefix tailTrace_1866540
  have hstable : (prefixWord ++ tailWord_1866540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866540).length < 2 ^ (prefixWord ++ tailWord_1866540).sum := by decide
  have hdescent : baseEnd_1866540 < baseStart_1866540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866548 : List Nat := [2, 5, 1, 1, 4, 1, 1, 3, 1, 2, 2]
def baseStart_1866548 : Nat := 118140960795 + 1866548 * 2 ^ 59
def prefixEnd_1866548 : Nat := 4983230072969 + 3 ^ 40 * 1866548 * 2
def baseEnd_1866548 : Nat := 958436288688468356065909

theorem tailTrace_1866548 : CollatzResearch.WordTrace tailWord_1866548 prefixEnd_1866548 958436288688468356065909 := by
  unfold tailWord_1866548
  simp only [CollatzResearch.WordTrace]
  refine ⟨34039299220911425932028149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45385732294548567909370865 34039299220911425932028149)
  ·
    refine ⟨3191184301960446181127639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34039299220911425932028149 3191184301960446181127639)
    ·
      refine ⟨4786776452940669271691459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3191184301960446181127639 4786776452940669271691459)
      ·
        refine ⟨7180164679411003907537189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4786776452940669271691459 7180164679411003907537189)
        ·
          refine ⟨1346280877389563232663223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7180164679411003907537189 1346280877389563232663223)
          ·
            refine ⟨2019421316084344848994835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1346280877389563232663223 2019421316084344848994835)
            ·
              refine ⟨3029131974126517273492253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2019421316084344848994835 3029131974126517273492253)
              ·
                refine ⟨1135924490297443977559595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3029131974126517273492253 1135924490297443977559595)
                ·
                  refine ⟨1703886735446165966339393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1135924490297443977559595 1703886735446165966339393)
                  ·
                    refine ⟨1277915051584624474754545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1703886735446165966339393 1277915051584624474754545)
                    ·
                      refine ⟨958436288688468356065909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1277915051584624474754545 958436288688468356065909)
                      ·
                        rfl

theorem cell23_1866548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_1866548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1866548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1866548 prefixEnd_1866548 := by exact prefixLift 1866548
  have htrace : WordTrace (prefixWord ++ tailWord_1866548) baseStart_1866548 baseEnd_1866548 := by
    simpa [prefixWord, tailWord_1866548, baseEnd_1866548] using wordTrace_append hprefix tailTrace_1866548
  have hstable : (prefixWord ++ tailWord_1866548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866548).length < 2 ^ (prefixWord ++ tailWord_1866548).sum := by decide
  have hdescent : baseEnd_1866548 < baseStart_1866548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866556 : List Nat := [2, 2, 2, 2, 1, 1, 1, 2, 1, 6, 3]
def baseStart_1866556 : Nat := 118140960795 + 1866556 * 2 ^ 59
def prefixEnd_1866556 : Nat := 4983230072969 + 3 ^ 40 * 1866556 * 2
def baseEnd_1866556 : Nat := 958440396533704324765871

theorem tailTrace_1866556 : CollatzResearch.WordTrace tailWord_1866556 prefixEnd_1866556 958440396533704324765871 := by
  unfold tailWord_1866556
  simp only [CollatzResearch.WordTrace]
  refine ⟨34039445112896934615173761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45385926817195912820231681 34039445112896934615173761)
  ·
    refine ⟨25529583834672700961380321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34039445112896934615173761 25529583834672700961380321)
    ·
      refine ⟨19147187876004525721035241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25529583834672700961380321 19147187876004525721035241)
      ·
        refine ⟨14360390907003394290776431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19147187876004525721035241 14360390907003394290776431)
        ·
          refine ⟨21540586360505091436164647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14360390907003394290776431 21540586360505091436164647)
          ·
            refine ⟨32310879540757637154246971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21540586360505091436164647 32310879540757637154246971)
            ·
              refine ⟨48466319311136455731370457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32310879540757637154246971 48466319311136455731370457)
              ·
                refine ⟨36349739483352341798527843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48466319311136455731370457 36349739483352341798527843)
                ·
                  refine ⟨54524609225028512697791765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36349739483352341798527843 54524609225028512697791765)
                  ·
                    refine ⟨2555841057423211532708989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 54524609225028512697791765 2555841057423211532708989)
                    ·
                      refine ⟨958440396533704324765871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2555841057423211532708989 958440396533704324765871)
                      ·
                        rfl

theorem cell23_1866556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_1866556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1866556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1866556 prefixEnd_1866556 := by exact prefixLift 1866556
  have htrace : WordTrace (prefixWord ++ tailWord_1866556) baseStart_1866556 baseEnd_1866556 := by
    simpa [prefixWord, tailWord_1866556, baseEnd_1866556] using wordTrace_append hprefix tailTrace_1866556
  have hstable : (prefixWord ++ tailWord_1866556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866556).length < 2 ^ (prefixWord ++ tailWord_1866556).sum := by decide
  have hdescent : baseEnd_1866556 < baseStart_1866556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866576 : List Nat := [2, 1, 1, 1, 1, 4, 5, 1, 7]
def baseStart_1866576 : Nat := 118140960795 + 1866576 * 2 ^ 59
def prefixEnd_1866576 : Nat := 4983230072969 + 3 ^ 40 * 1866576 * 2
def baseEnd_1866576 : Nat := 106494518460754916279531

theorem tailTrace_1866576 : CollatzResearch.WordTrace tailWord_1866576 prefixEnd_1866576 106494518460754916279531 := by
  unfold tailWord_1866576
  simp only [CollatzResearch.WordTrace]
  refine ⟨34039809842860706323037791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45386413123814275097383721 34039809842860706323037791)
  ·
    refine ⟨51059714764291059484556687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34039809842860706323037791 51059714764291059484556687)
    ·
      refine ⟨76589572146436589226835031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51059714764291059484556687 76589572146436589226835031)
      ·
        refine ⟨114884358219654883840252547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76589572146436589226835031 114884358219654883840252547)
        ·
          refine ⟨172326537329482325760378821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114884358219654883840252547 172326537329482325760378821)
          ·
            refine ⟨32311225749277936080071029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172326537329482325760378821 32311225749277936080071029)
            ·
              refine ⟨3029177413994806507506659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32311225749277936080071029 3029177413994806507506659)
              ·
                refine ⟨4543766120992209761259989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3029177413994806507506659 4543766120992209761259989)
                ·
                  refine ⟨106494518460754916279531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4543766120992209761259989 106494518460754916279531)
                  ·
                    rfl

theorem cell23_1866576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 1, 7].length) (baseStart_1866576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1866576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1866576 prefixEnd_1866576 := by exact prefixLift 1866576
  have htrace : WordTrace (prefixWord ++ tailWord_1866576) baseStart_1866576 baseEnd_1866576 := by
    simpa [prefixWord, tailWord_1866576, baseEnd_1866576] using wordTrace_append hprefix tailTrace_1866576
  have hstable : (prefixWord ++ tailWord_1866576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866576).length < 2 ^ (prefixWord ++ tailWord_1866576).sum := by decide
  have hdescent : baseEnd_1866576 < baseStart_1866576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866700 : List Nat := [2, 2, 1, 4, 1, 1, 5, 1, 6]
def baseStart_1866700 : Nat := 118140960795 + 1866700 * 2 ^ 59
def prefixEnd_1866700 : Nat := 4983230072969 + 3 ^ 40 * 1866700 * 2
def baseEnd_1866700 : Nat := 106501593083105751262801

theorem tailTrace_1866700 : CollatzResearch.WordTrace tailWord_1866700 prefixEnd_1866700 106501593083105751262801 := by
  unfold tailWord_1866700
  simp only [CollatzResearch.WordTrace]
  refine ⟨34042071168636090911794777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45389428224848121215726369 34042071168636090911794777)
  ·
    refine ⟨25531553376477068183846083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34042071168636090911794777 25531553376477068183846083)
    ·
      refine ⟨38297330064715602275769125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25531553376477068183846083 38297330064715602275769125)
      ·
        refine ⟨7180749387134175426706711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38297330064715602275769125 7180749387134175426706711)
        ·
          refine ⟨10771124080701263140060067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7180749387134175426706711 10771124080701263140060067)
          ·
            refine ⟨16156686121051894710090101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10771124080701263140060067 16156686121051894710090101)
            ·
              refine ⟨1514689323848615129070947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16156686121051894710090101 1514689323848615129070947)
              ·
                refine ⟨2272033985772922693606421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1514689323848615129070947 2272033985772922693606421)
                ·
                  refine ⟨106501593083105751262801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2272033985772922693606421 106501593083105751262801)
                  ·
                    rfl

theorem cell23_1866700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5, 1, 6].length) (baseStart_1866700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1866700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1866700 prefixEnd_1866700 := by exact prefixLift 1866700
  have htrace : WordTrace (prefixWord ++ tailWord_1866700) baseStart_1866700 baseEnd_1866700 := by
    simpa [prefixWord, tailWord_1866700, baseEnd_1866700] using wordTrace_append hprefix tailTrace_1866700
  have hstable : (prefixWord ++ tailWord_1866700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866700).length < 2 ^ (prefixWord ++ tailWord_1866700).sum := by decide
  have hdescent : baseEnd_1866700 < baseStart_1866700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866730 : List Nat := [3, 1, 3, 1, 2, 2, 2, 3, 1, 5]
def baseStart_1866730 : Nat := 118140960795 + 1866730 * 2 ^ 59
def prefixEnd_1866730 : Nat := 4983230072969 + 3 ^ 40 * 1866730 * 2
def baseEnd_1866730 : Nat := 319509914055862214663357

theorem tailTrace_1866730 : CollatzResearch.WordTrace tailWord_1866730 prefixEnd_1866730 319509914055862214663357 := by
  unfold tailWord_1866730
  simp only [CollatzResearch.WordTrace]
  refine ⟨17021309131790874236795411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45390157684775664631454429 17021309131790874236795411)
  ·
    refine ⟨25531963697686311355193117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17021309131790874236795411 25531963697686311355193117)
    ·
      refine ⟨9574486386632366758197419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25531963697686311355193117 9574486386632366758197419)
      ·
        refine ⟨14361729579948550137296129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9574486386632366758197419 14361729579948550137296129)
        ·
          refine ⟨10771297184961412602972097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14361729579948550137296129 10771297184961412602972097)
          ·
            refine ⟨8078472888721059452229073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10771297184961412602972097 8078472888721059452229073)
            ·
              refine ⟨6058854666540794589171805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8078472888721059452229073 6058854666540794589171805)
              ·
                refine ⟨2272070499952797970939427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6058854666540794589171805 2272070499952797970939427)
                ·
                  refine ⟨3408105749929196956409141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2272070499952797970939427 3408105749929196956409141)
                  ·
                    refine ⟨319509914055862214663357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3408105749929196956409141 319509914055862214663357)
                    ·
                      rfl

theorem cell23_1866730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_1866730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1866730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1866730 prefixEnd_1866730 := by exact prefixLift 1866730
  have htrace : WordTrace (prefixWord ++ tailWord_1866730) baseStart_1866730 baseEnd_1866730 := by
    simpa [prefixWord, tailWord_1866730, baseEnd_1866730] using wordTrace_append hprefix tailTrace_1866730
  have hstable : (prefixWord ++ tailWord_1866730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866730).length < 2 ^ (prefixWord ++ tailWord_1866730).sum := by decide
  have hdescent : baseEnd_1866730 < baseStart_1866730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866737 : List Nat := [1, 2, 2, 2, 4, 2, 1, 2, 2, 3, 2]
def baseStart_1866737 : Nat := 118140960795 + 1866737 * 2 ^ 59
def prefixEnd_1866737 : Nat := 4983230072969 + 3 ^ 40 * 1866737 * 2
def baseEnd_1866737 : Nat := 958533336532168116602539

theorem tailTrace_1866737 : CollatzResearch.WordTrace tailWord_1866737 prefixEnd_1866737 958533336532168116602539 := by
  unfold tailWord_1866737
  simp only [CollatzResearch.WordTrace]
  refine ⟨68085491838138137142686465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45390327892092091428457643 68085491838138137142686465)
  ·
    refine ⟨51064118878603602857014849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68085491838138137142686465 51064118878603602857014849)
    ·
      refine ⟨38298089158952702142761137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51064118878603602857014849 38298089158952702142761137)
      ·
        refine ⟨28723566869214526607070853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38298089158952702142761137 28723566869214526607070853)
        ·
          refine ⟨5385668787977723738825785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28723566869214526607070853 5385668787977723738825785)
          ·
            refine ⟨4039251590983292804119339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5385668787977723738825785 4039251590983292804119339)
            ·
              refine ⟨6058877386474939206179009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4039251590983292804119339 6058877386474939206179009)
              ·
                refine ⟨4544158039856204404634257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6058877386474939206179009 4544158039856204404634257)
                ·
                  refine ⟨3408118529892153303475693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4544158039856204404634257 3408118529892153303475693)
                  ·
                    refine ⟨1278044448709557488803385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3408118529892153303475693 1278044448709557488803385)
                    ·
                      refine ⟨958533336532168116602539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1278044448709557488803385 958533336532168116602539)
                      ·
                        rfl

theorem cell23_1866737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 2, 2, 3, 2].length) (baseStart_1866737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1866737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1866737 prefixEnd_1866737 := by exact prefixLift 1866737
  have htrace : WordTrace (prefixWord ++ tailWord_1866737) baseStart_1866737 baseEnd_1866737 := by
    simpa [prefixWord, tailWord_1866737, baseEnd_1866737] using wordTrace_append hprefix tailTrace_1866737
  have hstable : (prefixWord ++ tailWord_1866737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866737).length < 2 ^ (prefixWord ++ tailWord_1866737).sum := by decide
  have hdescent : baseEnd_1866737 < baseStart_1866737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866763 : List Nat := [1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 6]
def baseStart_1866763 : Nat := 118140960795 + 1866763 * 2 ^ 59
def prefixEnd_1866763 : Nat := 4983230072969 + 3 ^ 40 * 1866763 * 2
def baseEnd_1866763 : Nat := 958546687029185014877419

theorem tailTrace_1866763 : CollatzResearch.WordTrace tailWord_1866763 prefixEnd_1866763 958546687029185014877419 := by
  unfold tailWord_1866763
  simp only [CollatzResearch.WordTrace]
  refine ⟨68086440136043943583132943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45390960090695962388755295 68086440136043943583132943)
  ·
    refine ⟨102129660204065915374699415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68086440136043943583132943 102129660204065915374699415)
    ·
      refine ⟨153194490306098873062049123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102129660204065915374699415 153194490306098873062049123)
      ·
        refine ⟨229791735459148309593073685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153194490306098873062049123 229791735459148309593073685)
        ·
          refine ⟨10771487599647577012175329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 229791735459148309593073685 10771487599647577012175329)
          ·
            refine ⟨8078615699735682759131497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10771487599647577012175329 8078615699735682759131497)
            ·
              refine ⟨6058961774801762069348623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8078615699735682759131497 6058961774801762069348623)
              ·
                refine ⟨9088442662202643104022935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6058961774801762069348623 9088442662202643104022935)
                ·
                  refine ⟨13632663993303964656034403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9088442662202643104022935 13632663993303964656034403)
                  ·
                    refine ⟨20448995989955946984051605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13632663993303964656034403 20448995989955946984051605)
                    ·
                      refine ⟨958546687029185014877419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20448995989955946984051605 958546687029185014877419)
                      ·
                        rfl

theorem cell23_1866763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 6].length) (baseStart_1866763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1866763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1866763 prefixEnd_1866763 := by exact prefixLift 1866763
  have htrace : WordTrace (prefixWord ++ tailWord_1866763) baseStart_1866763 baseEnd_1866763 := by
    simpa [prefixWord, tailWord_1866763, baseEnd_1866763] using wordTrace_append hprefix tailTrace_1866763
  have hstable : (prefixWord ++ tailWord_1866763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866763).length < 2 ^ (prefixWord ++ tailWord_1866763).sum := by decide
  have hdescent : baseEnd_1866763 < baseStart_1866763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866773 : List Nat := [1, 3, 2, 1, 4, 1, 2, 9]
def baseStart_1866773 : Nat := 118140960795 + 1866773 * 2 ^ 59
def prefixEnd_1866773 : Nat := 4983230072969 + 3 ^ 40 * 1866773 * 2
def baseEnd_1866773 : Nat := 35501919327249258361199

theorem tailTrace_1866773 : CollatzResearch.WordTrace tailWord_1866773 prefixEnd_1866773 35501919327249258361199 := by
  unfold tailWord_1866773
  simp only [CollatzResearch.WordTrace]
  refine ⟨68086804866007715290996973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45391203244005143527331315 68086804866007715290996973)
  ·
    refine ⟨25532551824752893234123865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68086804866007715290996973 25532551824752893234123865)
    ·
      refine ⟨19149413868564669925592899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25532551824752893234123865 19149413868564669925592899)
      ·
        refine ⟨28724120802847004888389349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19149413868564669925592899 28724120802847004888389349)
        ·
          refine ⟨5385772650533813416573003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28724120802847004888389349 5385772650533813416573003)
          ·
            refine ⟨8078658975800720124859505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5385772650533813416573003 8078658975800720124859505)
            ·
              refine ⟨6058994231850540093644629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8078658975800720124859505 6058994231850540093644629)
              ·
                refine ⟨35501919327249258361199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6058994231850540093644629 35501919327249258361199)
                ·
                  rfl

theorem cell23_1866773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 9].length) (baseStart_1866773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1866773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1866773 prefixEnd_1866773 := by exact prefixLift 1866773
  have htrace : WordTrace (prefixWord ++ tailWord_1866773) baseStart_1866773 baseEnd_1866773 := by
    simpa [prefixWord, tailWord_1866773, baseEnd_1866773] using wordTrace_append hprefix tailTrace_1866773
  have hstable : (prefixWord ++ tailWord_1866773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866773).length < 2 ^ (prefixWord ++ tailWord_1866773).sum := by decide
  have hdescent : baseEnd_1866773 < baseStart_1866773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866794 : List Nat := [3, 1, 4, 1, 3, 1, 2, 2, 2, 4]
def baseStart_1866794 : Nat := 118140960795 + 1866794 * 2 ^ 59
def prefixEnd_1866794 : Nat := 4983230072969 + 3 ^ 40 * 1866794 * 2
def baseEnd_1866794 : Nat := 319520868309824797863259

theorem tailTrace_1866794 : CollatzResearch.WordTrace tailWord_1866794 prefixEnd_1866794 319520868309824797863259 := by
  unfold tailWord_1866794
  simp only [CollatzResearch.WordTrace]
  refine ⟨17021892699732908969377859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45391713865954423918340957 17021892699732908969377859)
  ·
    refine ⟨25532839049599363454066789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17021892699732908969377859 25532839049599363454066789)
    ·
      refine ⟨4787407321799880647637523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25532839049599363454066789 4787407321799880647637523)
      ·
        refine ⟨7181110982699820971456285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4787407321799880647637523 7181110982699820971456285)
        ·
          refine ⟨2692916618512432864296107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7181110982699820971456285 2692916618512432864296107)
          ·
            refine ⟨4039374927768649296444161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2692916618512432864296107 4039374927768649296444161)
            ·
              refine ⟨3029531195826486972333121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4039374927768649296444161 3029531195826486972333121)
              ·
                refine ⟨2272148396869865229249841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3029531195826486972333121 2272148396869865229249841)
                ·
                  refine ⟨1704111297652398921937381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2272148396869865229249841 1704111297652398921937381)
                  ·
                    refine ⟨319520868309824797863259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1704111297652398921937381 319520868309824797863259)
                    ·
                      rfl

theorem cell23_1866794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_1866794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1866794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1866794 prefixEnd_1866794 := by exact prefixLift 1866794
  have htrace : WordTrace (prefixWord ++ tailWord_1866794) baseStart_1866794 baseEnd_1866794 := by
    simpa [prefixWord, tailWord_1866794, baseEnd_1866794] using wordTrace_append hprefix tailTrace_1866794
  have hstable : (prefixWord ++ tailWord_1866794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866794).length < 2 ^ (prefixWord ++ tailWord_1866794).sum := by decide
  have hdescent : baseEnd_1866794 < baseStart_1866794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866844 : List Nat := [2, 2, 4, 1, 1, 1, 3, 3, 1, 3, 2]
def baseStart_1866844 : Nat := 118140960795 + 1866844 * 2 ^ 59
def prefixEnd_1866844 : Nat := 4983230072969 + 3 ^ 40 * 1866844 * 2
def baseEnd_1866844 : Nat := 958588278962199197964547

theorem tailTrace_1866844 : CollatzResearch.WordTrace tailWord_1866844 prefixEnd_1866844 958588278962199197964547 := by
  unfold tailWord_1866844
  simp only [CollatzResearch.WordTrace]
  refine ⟨34044697224375247208415793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45392929632500329611221057 34044697224375247208415793)
  ·
    refine ⟨25533522918281435406311845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34044697224375247208415793 25533522918281435406311845)
    ·
      refine ⟨4787535547177769138683471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25533522918281435406311845 4787535547177769138683471)
      ·
        refine ⟨7181303320766653708025207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4787535547177769138683471 7181303320766653708025207)
        ·
          refine ⟨10771954981149980562037811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7181303320766653708025207 10771954981149980562037811)
          ·
            refine ⟨16157932471724970843056717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10771954981149980562037811 16157932471724970843056717)
            ·
              refine ⟨6059224676896864066146269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16157932471724970843056717 6059224676896864066146269)
              ·
                refine ⟨2272209253836324024804851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6059224676896864066146269 2272209253836324024804851)
                ·
                  refine ⟨3408313880754486037207277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2272209253836324024804851 3408313880754486037207277)
                  ·
                    refine ⟨1278117705282932263952729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3408313880754486037207277 1278117705282932263952729)
                    ·
                      refine ⟨958588278962199197964547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1278117705282932263952729 958588278962199197964547)
                      ·
                        rfl

theorem cell23_1866844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_1866844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1866844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1866844 prefixEnd_1866844 := by exact prefixLift 1866844
  have htrace : WordTrace (prefixWord ++ tailWord_1866844) baseStart_1866844 baseEnd_1866844 := by
    simpa [prefixWord, tailWord_1866844, baseEnd_1866844] using wordTrace_append hprefix tailTrace_1866844
  have hstable : (prefixWord ++ tailWord_1866844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866844).length < 2 ^ (prefixWord ++ tailWord_1866844).sum := by decide
  have hdescent : baseEnd_1866844 < baseStart_1866844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866914 : List Nat := [3, 3, 1, 3, 2, 2, 1, 1, 7]
def baseStart_1866914 : Nat := 118140960795 + 1866914 * 2 ^ 59
def prefixEnd_1866914 : Nat := 4983230072969 + 3 ^ 40 * 1866914 * 2
def baseEnd_1866914 : Nat := 106513802512001547121025

theorem tailTrace_1866914 : CollatzResearch.WordTrace tailWord_1866914 prefixEnd_1866914 106513802512001547121025 := by
  unfold tailWord_1866914
  simp only [CollatzResearch.WordTrace]
  refine ⟨17022986889624224092969949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45394631705664597581253197 17022986889624224092969949)
  ·
    refine ⟨6383620083609084034863731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17022986889624224092969949 6383620083609084034863731)
    ·
      refine ⟨9575430125413626052295597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6383620083609084034863731 9575430125413626052295597)
      ·
        refine ⟨3590786297030109769610849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9575430125413626052295597 3590786297030109769610849)
        ·
          refine ⟨2693089722772582327208137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3590786297030109769610849 2693089722772582327208137)
          ·
            refine ⟨2019817292079436745406103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2693089722772582327208137 2019817292079436745406103)
            ·
              refine ⟨3029725938119155118109155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2019817292079436745406103 3029725938119155118109155)
              ·
                refine ⟨4544588907178732677163733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3029725938119155118109155 4544588907178732677163733)
                ·
                  refine ⟨106513802512001547121025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4544588907178732677163733 106513802512001547121025)
                  ·
                    rfl

theorem cell23_1866914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 1, 7].length) (baseStart_1866914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1866914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1866914 prefixEnd_1866914 := by exact prefixLift 1866914
  have htrace : WordTrace (prefixWord ++ tailWord_1866914) baseStart_1866914 baseEnd_1866914 := by
    simpa [prefixWord, tailWord_1866914, baseEnd_1866914] using wordTrace_append hprefix tailTrace_1866914
  have hstable : (prefixWord ++ tailWord_1866914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866914).length < 2 ^ (prefixWord ++ tailWord_1866914).sum := by decide
  have hdescent : baseEnd_1866914 < baseStart_1866914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866925 : List Nat := [1, 5, 2, 1, 3, 2, 2, 1, 2, 2, 2]
def baseStart_1866925 : Nat := 118140960795 + 1866925 * 2 ^ 59
def prefixEnd_1866925 : Nat := 4983230072969 + 3 ^ 40 * 1866925 * 2
def baseEnd_1866925 : Nat := 958629870895213381051675

theorem tailTrace_1866925 : CollatzResearch.WordTrace tailWord_1866925 prefixEnd_1866925 958629870895213381051675 := by
  unfold tailWord_1866925
  simp only [CollatzResearch.WordTrace]
  refine ⟨68092348761457045250530229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45394899174304696833686819 68092348761457045250530229)
  ·
    refine ⟨6383657696386597992237209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68092348761457045250530229 6383657696386597992237209)
    ·
      refine ⟨4787743272289948494177907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6383657696386597992237209 4787743272289948494177907)
      ·
        refine ⟨7181614908434922741266861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4787743272289948494177907 7181614908434922741266861)
        ·
          refine ⟨2693105590663096027975073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7181614908434922741266861 2693105590663096027975073)
          ·
            refine ⟨2019829192997322020981305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2693105590663096027975073 2019829192997322020981305)
            ·
              refine ⟨1514871894747991515735979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2019829192997322020981305 1514871894747991515735979)
              ·
                refine ⟨2272307842121987273603969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1514871894747991515735979 2272307842121987273603969)
                ·
                  refine ⟨1704230881591490455202977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2272307842121987273603969 1704230881591490455202977)
                  ·
                    refine ⟨1278173161193617841402233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1704230881591490455202977 1278173161193617841402233)
                    ·
                      refine ⟨958629870895213381051675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1278173161193617841402233 958629870895213381051675)
                      ·
                        rfl

theorem cell23_1866925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_1866925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1866925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1866925 prefixEnd_1866925 := by exact prefixLift 1866925
  have htrace : WordTrace (prefixWord ++ tailWord_1866925) baseStart_1866925 baseEnd_1866925 := by
    simpa [prefixWord, tailWord_1866925, baseEnd_1866925] using wordTrace_append hprefix tailTrace_1866925
  have hstable : (prefixWord ++ tailWord_1866925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866925).length < 2 ^ (prefixWord ++ tailWord_1866925).sum := by decide
  have hdescent : baseEnd_1866925 < baseStart_1866925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866967 : List Nat := [1, 1, 3, 2, 1, 2, 4, 2, 2, 2, 3]
def baseStart_1866967 : Nat := 118140960795 + 1866967 * 2 ^ 59
def prefixEnd_1866967 : Nat := 4983230072969 + 3 ^ 40 * 1866967 * 2
def baseEnd_1866967 : Nat := 958651437082702216726481

theorem tailTrace_1866967 : CollatzResearch.WordTrace tailWord_1866967 prefixEnd_1866967 958651437082702216726481 := by
  unfold tailWord_1866967
  simp only [CollatzResearch.WordTrace]
  refine ⟨68093880627304886423559155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45395920418203257615706103 68093880627304886423559155)
  ·
    refine ⟨102140820940957329635338733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68093880627304886423559155 102140820940957329635338733)
    ·
      refine ⟨38302807852858998613252025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102140820940957329635338733 38302807852858998613252025)
      ·
        refine ⟨28727105889644248959939019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38302807852858998613252025 28727105889644248959939019)
        ·
          refine ⟨43090658834466373439908529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28727105889644248959939019 43090658834466373439908529)
          ·
            refine ⟨32317994125849780079931397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43090658834466373439908529 32317994125849780079931397)
            ·
              refine ⟨6059623898596833764987137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32317994125849780079931397 6059623898596833764987137)
              ·
                refine ⟨4544717923947625323740353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6059623898596833764987137 4544717923947625323740353)
                ·
                  refine ⟨3408538442960718992805265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4544717923947625323740353 3408538442960718992805265)
                  ·
                    refine ⟨2556403832220539244603949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3408538442960718992805265 2556403832220539244603949)
                    ·
                      refine ⟨958651437082702216726481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2556403832220539244603949 958651437082702216726481)
                      ·
                        rfl

theorem cell23_1866967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 2, 2, 2, 3].length) (baseStart_1866967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1866967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1866967 prefixEnd_1866967 := by exact prefixLift 1866967
  have htrace : WordTrace (prefixWord ++ tailWord_1866967) baseStart_1866967 baseEnd_1866967 := by
    simpa [prefixWord, tailWord_1866967, baseEnd_1866967] using wordTrace_append hprefix tailTrace_1866967
  have hstable : (prefixWord ++ tailWord_1866967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866967).length < 2 ^ (prefixWord ++ tailWord_1866967).sum := by decide
  have hdescent : baseEnd_1866967 < baseStart_1866967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867017 : List Nat := [1, 2, 1, 1, 3, 3, 3, 3, 1, 5]
def baseStart_1867017 : Nat := 118140960795 + 1867017 * 2 ^ 59
def prefixEnd_1867017 : Nat := 4983230072969 + 3 ^ 40 * 1867017 * 2
def baseEnd_1867017 : Nat := 319559037038475673700417

theorem tailTrace_1867017 : CollatzResearch.WordTrace tailWord_1867017 prefixEnd_1867017 319559037038475673700417 := by
  unfold tailWord_1867017
  simp only [CollatzResearch.WordTrace]
  refine ⟨68095704277123744962879305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45397136184749163308586203 68095704277123744962879305)
  ·
    refine ⟨51071778207842808722159479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68095704277123744962879305 51071778207842808722159479)
    ·
      refine ⟨76607667311764213083239219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51071778207842808722159479 76607667311764213083239219)
      ·
        refine ⟨114911500967646319624858829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76607667311764213083239219 114911500967646319624858829)
        ·
          refine ⟨43091812862867369859322061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114911500967646319624858829 43091812862867369859322061)
          ·
            refine ⟨16159429823575263697245773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43091812862867369859322061 16159429823575263697245773)
            ·
              refine ⟨6059786183840723886467165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16159429823575263697245773 6059786183840723886467165)
              ·
                refine ⟨2272419818940271457425187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6059786183840723886467165 2272419818940271457425187)
                ·
                  refine ⟨3408629728410407186137781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2272419818940271457425187 3408629728410407186137781)
                  ·
                    refine ⟨319559037038475673700417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3408629728410407186137781 319559037038475673700417)
                    ·
                      rfl

theorem cell23_1867017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 3, 1, 5].length) (baseStart_1867017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1867017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1867017 prefixEnd_1867017 := by exact prefixLift 1867017
  have htrace : WordTrace (prefixWord ++ tailWord_1867017) baseStart_1867017 baseEnd_1867017 := by
    simpa [prefixWord, tailWord_1867017, baseEnd_1867017] using wordTrace_append hprefix tailTrace_1867017
  have hstable : (prefixWord ++ tailWord_1867017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867017).length < 2 ^ (prefixWord ++ tailWord_1867017).sum := by decide
  have hdescent : baseEnd_1867017 < baseStart_1867017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867031 : List Nat := [1, 1, 3, 4, 1, 1, 1, 6, 1, 1, 3]
def baseStart_1867031 : Nat := 118140960795 + 1867031 * 2 ^ 59
def prefixEnd_1867031 : Nat := 4983230072969 + 3 ^ 40 * 1867031 * 2
def baseEnd_1867031 : Nat := 958684299844589966326187

theorem tailTrace_1867031 : CollatzResearch.WordTrace tailWord_1867031 prefixEnd_1867031 958684299844589966326187 := by
  unfold tailWord_1867031
  simp only [CollatzResearch.WordTrace]
  refine ⟨68096214899073025353888947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45397476599382016902592631 68096214899073025353888947)
  ·
    refine ⟨102144322348609538030833421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68096214899073025353888947 102144322348609538030833421)
    ·
      refine ⟨38304120880728576761562533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102144322348609538030833421 38304120880728576761562533)
      ·
        refine ⟨7182022665136608142792975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38304120880728576761562533 7182022665136608142792975)
        ·
          refine ⟨10773033997704912214189463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7182022665136608142792975 10773033997704912214189463)
          ·
            refine ⟨16159550996557368321284195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10773033997704912214189463 16159550996557368321284195)
            ·
              refine ⟨24239326494836052481926293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16159550996557368321284195 24239326494836052481926293)
              ·
                refine ⟨1136218429445439960090295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24239326494836052481926293 1136218429445439960090295)
                ·
                  refine ⟨1704327644168159940135443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1136218429445439960090295 1704327644168159940135443)
                  ·
                    refine ⟨2556491466252239910203165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1704327644168159940135443 2556491466252239910203165)
                    ·
                      refine ⟨958684299844589966326187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2556491466252239910203165 958684299844589966326187)
                      ·
                        rfl

theorem cell23_1867031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_1867031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1867031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1867031 prefixEnd_1867031 := by exact prefixLift 1867031
  have htrace : WordTrace (prefixWord ++ tailWord_1867031) baseStart_1867031 baseEnd_1867031 := by
    simpa [prefixWord, tailWord_1867031, baseEnd_1867031] using wordTrace_append hprefix tailTrace_1867031
  have hstable : (prefixWord ++ tailWord_1867031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867031).length < 2 ^ (prefixWord ++ tailWord_1867031).sum := by decide
  have hdescent : baseEnd_1867031 < baseStart_1867031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867038 : List Nat := [4, 3, 2, 1, 2, 1, 3, 1, 6]
def baseStart_1867038 : Nat := 118140960795 + 1867038 * 2 ^ 59
def prefixEnd_1867038 : Nat := 4983230072969 + 3 ^ 40 * 1867038 * 2
def baseEnd_1867038 : Nat := 106520877134352382104295

theorem tailTrace_1867038 : CollatzResearch.WordTrace tailWord_1867038 prefixEnd_1867038 106520877134352382104295 := by
  unfold tailWord_1867038
  simp only [CollatzResearch.WordTrace]
  refine ⟨8512058776255958193674221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45397646806698443699595845 8512058776255958193674221)
  ·
    refine ⟨3192022041095984322627833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8512058776255958193674221 3192022041095984322627833)
    ·
      refine ⟨2394016530821988241970875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3192022041095984322627833 2394016530821988241970875)
      ·
        refine ⟨3591024796232982362956313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2394016530821988241970875 3591024796232982362956313)
        ·
          refine ⟨2693268597174736772217235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3591024796232982362956313 2693268597174736772217235)
          ·
            refine ⟨4039902895762105158325853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2693268597174736772217235 4039902895762105158325853)
            ·
              refine ⟨1514963585910789434372195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4039902895762105158325853 1514963585910789434372195)
              ·
                refine ⟨2272445378866184151558293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1514963585910789434372195 2272445378866184151558293)
                ·
                  refine ⟨106520877134352382104295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2272445378866184151558293 106520877134352382104295)
                  ·
                    rfl

theorem cell23_1867038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_1867038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1867038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1867038 prefixEnd_1867038 := by exact prefixLift 1867038
  have htrace : WordTrace (prefixWord ++ tailWord_1867038) baseStart_1867038 baseEnd_1867038 := by
    simpa [prefixWord, tailWord_1867038, baseEnd_1867038] using wordTrace_append hprefix tailTrace_1867038
  have hstable : (prefixWord ++ tailWord_1867038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867038).length < 2 ^ (prefixWord ++ tailWord_1867038).sum := by decide
  have hdescent : baseEnd_1867038 < baseStart_1867038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867065 : List Nat := [1, 2, 1, 6, 2, 2, 1, 3, 1, 1, 3]
def baseStart_1867065 : Nat := 118140960795 + 1867065 * 2 ^ 59
def prefixEnd_1867065 : Nat := 4983230072969 + 3 ^ 40 * 1867065 * 2
def baseEnd_1867065 : Nat := 958701758186842833301031

theorem tailTrace_1867065 : CollatzResearch.WordTrace tailWord_1867065 prefixEnd_1867065 958701758186842833301031 := by
  unfold tailWord_1867065
  simp only [CollatzResearch.WordTrace]
  refine ⟨68097454980949849160626649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45398303320633232773751099 68097454980949849160626649)
  ·
    refine ⟨51073091235712386870469987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68097454980949849160626649 51073091235712386870469987)
    ·
      refine ⟨76609636853568580305704981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51073091235712386870469987 76609636853568580305704981)
      ·
        refine ⟨3591076727511027201829921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 76609636853568580305704981 3591076727511027201829921)
        ·
          refine ⟨2693307545633270401372441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3591076727511027201829921 2693307545633270401372441)
          ·
            refine ⟨2019980659224952801029331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2693307545633270401372441 2019980659224952801029331)
            ·
              refine ⟨3029970988837429201543997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2019980659224952801029331 3029970988837429201543997)
              ·
                refine ⟨1136239120814035950578999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3029970988837429201543997 1136239120814035950578999)
                ·
                  refine ⟨1704358681221053925868499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1136239120814035950578999 1704358681221053925868499)
                  ·
                    refine ⟨2556538021831580888802749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1704358681221053925868499 2556538021831580888802749)
                    ·
                      refine ⟨958701758186842833301031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2556538021831580888802749 958701758186842833301031)
                      ·
                        rfl

theorem cell23_1867065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_1867065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1867065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1867065 prefixEnd_1867065 := by exact prefixLift 1867065
  have htrace : WordTrace (prefixWord ++ tailWord_1867065) baseStart_1867065 baseEnd_1867065 := by
    simpa [prefixWord, tailWord_1867065, baseEnd_1867065] using wordTrace_append hprefix tailTrace_1867065
  have hstable : (prefixWord ++ tailWord_1867065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867065).length < 2 ^ (prefixWord ++ tailWord_1867065).sum := by decide
  have hdescent : baseEnd_1867065 < baseStart_1867065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867147 : List Nat := [1, 1, 1, 1, 4, 3, 1, 1, 1, 6, 3]
def baseStart_1867147 : Nat := 118140960795 + 1867147 * 2 ^ 59
def prefixEnd_1867147 : Nat := 4983230072969 + 3 ^ 40 * 1867147 * 2
def baseEnd_1867147 : Nat := 958743863600511512475653

theorem tailTrace_1867147 : CollatzResearch.WordTrace tailWord_1867147 prefixEnd_1867147 958743863600511512475653 := by
  unfold tailWord_1867147
  simp only [CollatzResearch.WordTrace]
  refine ⟨68100445766652777165111695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45400297177768518110074463 68100445766652777165111695)
  ·
    refine ⟨102150668649979165747667543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68100445766652777165111695 102150668649979165747667543)
    ·
      refine ⟨153226002974968748621501315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102150668649979165747667543 153226002974968748621501315)
      ·
        refine ⟨229839004462453122932251973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153226002974968748621501315 229839004462453122932251973)
        ·
          refine ⟨43094813336709960549797245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 229839004462453122932251973 43094813336709960549797245)
          ·
            refine ⟨16160555001266235206173967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43094813336709960549797245 16160555001266235206173967)
            ·
              refine ⟨24240832501899352809260951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16160555001266235206173967 24240832501899352809260951)
              ·
                refine ⟨36361248752849029213891427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24240832501899352809260951 36361248752849029213891427)
                ·
                  refine ⟨54541873129273543820837141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36361248752849029213891427 54541873129273543820837141)
                  ·
                    refine ⟨2556650302934697366601741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 54541873129273543820837141 2556650302934697366601741)
                    ·
                      refine ⟨958743863600511512475653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2556650302934697366601741 958743863600511512475653)
                      ·
                        rfl

theorem cell23_1867147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 6, 3].length) (baseStart_1867147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1867147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1867147 prefixEnd_1867147 := by exact prefixLift 1867147
  have htrace : WordTrace (prefixWord ++ tailWord_1867147) baseStart_1867147 baseEnd_1867147 := by
    simpa [prefixWord, tailWord_1867147, baseEnd_1867147] using wordTrace_append hprefix tailTrace_1867147
  have hstable : (prefixWord ++ tailWord_1867147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867147).length < 2 ^ (prefixWord ++ tailWord_1867147).sum := by decide
  have hdescent : baseEnd_1867147 < baseStart_1867147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867157 : List Nat := [1, 3, 2, 1, 1, 2, 3, 1, 1, 4, 4]
def baseStart_1867157 : Nat := 118140960795 + 1867157 * 2 ^ 59
def prefixEnd_1867157 : Nat := 4983230072969 + 3 ^ 40 * 1867157 * 2
def baseEnd_1867157 : Nat := 958748998407056473350607

theorem tailTrace_1867157 : CollatzResearch.WordTrace tailWord_1867157 prefixEnd_1867157 958748998407056473350607 := by
  unfold tailWord_1867157
  simp only [CollatzResearch.WordTrace]
  refine ⟨68100810496616548872975725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45400540331077699248650483 68100810496616548872975725)
  ·
    refine ⟨25537803936231205827365897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68100810496616548872975725 25537803936231205827365897)
    ·
      refine ⟨19153352952173404370524423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25537803936231205827365897 19153352952173404370524423)
      ·
        refine ⟨28730029428260106555786635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19153352952173404370524423 28730029428260106555786635)
        ·
          refine ⟨43095044142390159833679953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28730029428260106555786635 43095044142390159833679953)
          ·
            refine ⟨32321283106792619875259965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43095044142390159833679953 32321283106792619875259965)
            ·
              refine ⟨12120481165047232453222487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32321283106792619875259965 12120481165047232453222487)
              ·
                refine ⟨18180721747570848679833731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12120481165047232453222487 18180721747570848679833731)
                ·
                  refine ⟨27271082621356273019750597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18180721747570848679833731 27271082621356273019750597)
                  ·
                    refine ⟨5113327991504301191203237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27271082621356273019750597 5113327991504301191203237)
                    ·
                      refine ⟨958748998407056473350607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5113327991504301191203237 958748998407056473350607)
                      ·
                        rfl

theorem cell23_1867157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_1867157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1867157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1867157 prefixEnd_1867157 := by exact prefixLift 1867157
  have htrace : WordTrace (prefixWord ++ tailWord_1867157) baseStart_1867157 baseEnd_1867157 := by
    simpa [prefixWord, tailWord_1867157, baseEnd_1867157] using wordTrace_append hprefix tailTrace_1867157
  have hstable : (prefixWord ++ tailWord_1867157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867157).length < 2 ^ (prefixWord ++ tailWord_1867157).sum := by decide
  have hdescent : baseEnd_1867157 < baseStart_1867157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867161 : List Nat := [1, 2, 1, 2, 1, 6, 2, 1, 1, 4, 2]
def baseStart_1867161 : Nat := 118140960795 + 1867161 * 2 ^ 59
def prefixEnd_1867161 : Nat := 4983230072969 + 3 ^ 40 * 1867161 * 2
def baseEnd_1867161 : Nat := 958751052329674457700589

theorem tailTrace_1867161 : CollatzResearch.WordTrace tailWord_1867161 prefixEnd_1867161 958751052329674457700589 := by
  unfold tailWord_1867161
  simp only [CollatzResearch.WordTrace]
  refine ⟨68100956388602057556121337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45400637592401371704080891 68100956388602057556121337)
  ·
    refine ⟨51075717291451543167091003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68100956388602057556121337 51075717291451543167091003)
    ·
      refine ⟨76613575937177314750636505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51075717291451543167091003 76613575937177314750636505)
      ·
        refine ⟨57460181952882986062977379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76613575937177314750636505 57460181952882986062977379)
        ·
          refine ⟨86190272929324479094466069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57460181952882986062977379 86190272929324479094466069)
          ·
            refine ⟨4040169043562084957553097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 86190272929324479094466069 4040169043562084957553097)
            ·
              refine ⟨3030126782671563718164823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4040169043562084957553097 3030126782671563718164823)
              ·
                refine ⟨4545190174007345577247235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3030126782671563718164823 4545190174007345577247235)
                ·
                  refine ⟨6817785261011018365870853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4545190174007345577247235 6817785261011018365870853)
                  ·
                    refine ⟨1278334736439565943600785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6817785261011018365870853 1278334736439565943600785)
                    ·
                      refine ⟨958751052329674457700589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1278334736439565943600785 958751052329674457700589)
                      ·
                        rfl

theorem cell23_1867161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 1, 1, 4, 2].length) (baseStart_1867161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1867161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1867161 prefixEnd_1867161 := by exact prefixLift 1867161
  have htrace : WordTrace (prefixWord ++ tailWord_1867161) baseStart_1867161 baseEnd_1867161 := by
    simpa [prefixWord, tailWord_1867161, baseEnd_1867161] using wordTrace_append hprefix tailTrace_1867161
  have hstable : (prefixWord ++ tailWord_1867161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867161).length < 2 ^ (prefixWord ++ tailWord_1867161).sum := by decide
  have hdescent : baseEnd_1867161 < baseStart_1867161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867167 : List Nat := [1, 1, 2, 5, 1, 2, 1, 1, 9]
def baseStart_1867167 : Nat := 118140960795 + 1867167 * 2 ^ 59
def prefixEnd_1867167 : Nat := 4983230072969 + 3 ^ 40 * 1867167 * 2
def baseEnd_1867167 : Nat := 106528237023733492691729

theorem tailTrace_1867167 : CollatzResearch.WordTrace tailWord_1867167 prefixEnd_1867167 106528237023733492691729 := by
  unfold tailWord_1867167
  simp only [CollatzResearch.WordTrace]
  refine ⟨68101175226580320580839755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45400783484386880387226503 68101175226580320580839755)
  ·
    refine ⟨102151762839870480871259633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68101175226580320580839755 102151762839870480871259633)
    ·
      refine ⟨76613822129902860653444725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102151762839870480871259633 76613822129902860653444725)
      ·
        refine ⟨7182545824678393186260443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76613822129902860653444725 7182545824678393186260443)
        ·
          refine ⟨10773818737017589779390665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7182545824678393186260443 10773818737017589779390665)
          ·
            refine ⟨8080364052763192334542999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10773818737017589779390665 8080364052763192334542999)
            ·
              refine ⟨12120546079144788501814499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8080364052763192334542999 12120546079144788501814499)
              ·
                refine ⟨18180819118717182752721749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12120546079144788501814499 18180819118717182752721749)
                ·
                  refine ⟨106528237023733492691729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 18180819118717182752721749 106528237023733492691729)
                  ·
                    rfl

theorem cell23_1867167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 9].length) (baseStart_1867167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1867167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1867167 prefixEnd_1867167 := by exact prefixLift 1867167
  have htrace : WordTrace (prefixWord ++ tailWord_1867167) baseStart_1867167 baseEnd_1867167 := by
    simpa [prefixWord, tailWord_1867167, baseEnd_1867167] using wordTrace_append hprefix tailTrace_1867167
  have hstable : (prefixWord ++ tailWord_1867167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867167).length < 2 ^ (prefixWord ++ tailWord_1867167).sum := by decide
  have hdescent : baseEnd_1867167 < baseStart_1867167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867207 : List Nat := [1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 7]
def baseStart_1867207 : Nat := 118140960795 + 1867207 * 2 ^ 59
def prefixEnd_1867207 : Nat := 4983230072969 + 3 ^ 40 * 1867207 * 2
def baseEnd_1867207 : Nat := 958774672439781277725377

theorem tailTrace_1867207 : CollatzResearch.WordTrace tailWord_1867207 prefixEnd_1867207 958774672439781277725377 := by
  unfold tailWord_1867207
  simp only [CollatzResearch.WordTrace]
  refine ⟨68102634146435407412295875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45401756097623604941530583 68102634146435407412295875)
  ·
    refine ⟨102153951219653111118443813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68102634146435407412295875 102153951219653111118443813)
    ·
      refine ⟨19153865853684958334708215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102153951219653111118443813 19153865853684958334708215)
      ·
        refine ⟨28730798780527437502062323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19153865853684958334708215 28730798780527437502062323)
        ·
          refine ⟨43096198170791156253093485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28730798780527437502062323 43096198170791156253093485)
          ·
            refine ⟨16161074314046683594910057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43096198170791156253093485 16161074314046683594910057)
            ·
              refine ⟨12120805735535012696182543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16161074314046683594910057 12120805735535012696182543)
              ·
                refine ⟨18181208603302519044273815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12120805735535012696182543 18181208603302519044273815)
                ·
                  refine ⟨27271812904953778566410723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18181208603302519044273815 27271812904953778566410723)
                  ·
                    refine ⟨40907719357430667849616085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27271812904953778566410723 40907719357430667849616085)
                    ·
                      refine ⟨958774672439781277725377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 40907719357430667849616085 958774672439781277725377)
                      ·
                        rfl

theorem cell23_1867207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_1867207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1867207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1867207 prefixEnd_1867207 := by exact prefixLift 1867207
  have htrace : WordTrace (prefixWord ++ tailWord_1867207) baseStart_1867207 baseEnd_1867207 := by
    simpa [prefixWord, tailWord_1867207, baseEnd_1867207] using wordTrace_append hprefix tailTrace_1867207
  have hstable : (prefixWord ++ tailWord_1867207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867207).length < 2 ^ (prefixWord ++ tailWord_1867207).sum := by decide
  have hdescent : baseEnd_1867207 < baseStart_1867207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867247 : List Nat := [1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 6]
def baseStart_1867247 : Nat := 118140960795 + 1867247 * 2 ^ 59
def prefixEnd_1867247 : Nat := 4983230072969 + 3 ^ 40 * 1867247 * 2
def baseEnd_1867247 : Nat := 958795211665961121225193

theorem tailTrace_1867247 : CollatzResearch.WordTrace tailWord_1867247 prefixEnd_1867247 958795211665961121225193 := by
  unfold tailWord_1867247
  simp only [CollatzResearch.WordTrace]
  refine ⟨68104093066290494243751995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45402728710860329495834663 68104093066290494243751995)
  ·
    refine ⟨102156139599435741365627993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68104093066290494243751995 102156139599435741365627993)
    ·
      refine ⟨76617104699576806024220995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102156139599435741365627993 76617104699576806024220995)
      ·
        refine ⟨114925657049365209036331493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76617104699576806024220995 114925657049365209036331493)
        ·
          refine ⟨21548560696755976694312155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114925657049365209036331493 21548560696755976694312155)
          ·
            refine ⟨32322841045133965041468233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21548560696755976694312155 32322841045133965041468233)
            ·
              refine ⟨24242130783850473781101175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32322841045133965041468233 24242130783850473781101175)
              ·
                refine ⟨36363196175775710671651763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24242130783850473781101175 36363196175775710671651763)
                ·
                  refine ⟨54544794263663566007477645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36363196175775710671651763 54544794263663566007477645)
                  ·
                    refine ⟨20454297848873837252804117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54544794263663566007477645 20454297848873837252804117)
                    ·
                      refine ⟨958795211665961121225193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20454297848873837252804117 958795211665961121225193)
                      ·
                        rfl

theorem cell23_1867247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 6].length) (baseStart_1867247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1867247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1867247 prefixEnd_1867247 := by exact prefixLift 1867247
  have htrace : WordTrace (prefixWord ++ tailWord_1867247) baseStart_1867247 baseEnd_1867247 := by
    simpa [prefixWord, tailWord_1867247, baseEnd_1867247] using wordTrace_append hprefix tailTrace_1867247
  have hstable : (prefixWord ++ tailWord_1867247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867247).length < 2 ^ (prefixWord ++ tailWord_1867247).sum := by decide
  have hdescent : baseEnd_1867247 < baseStart_1867247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867261 : List Nat := [1, 4, 1, 1, 1, 4, 3, 1, 3, 4]
def baseStart_1867261 : Nat := 118140960795 + 1867261 * 2 ^ 59
def prefixEnd_1867261 : Nat := 4983230072969 + 3 ^ 40 * 1867261 * 2
def baseEnd_1867261 : Nat := 319600800131708022150043

theorem tailTrace_1867261 : CollatzResearch.WordTrace tailWord_1867261 prefixEnd_1867261 319600800131708022150043 := by
  unfold tailWord_1867261
  simp only [CollatzResearch.WordTrace]
  refine ⟨68104603688239774634761637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45403069125493183089841091 68104603688239774634761637)
  ·
    refine ⟨12769613191544957744017807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68104603688239774634761637 12769613191544957744017807)
    ·
      refine ⟨19154419787317436616026711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12769613191544957744017807 19154419787317436616026711)
      ·
        refine ⟨28731629680976154924040067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19154419787317436616026711 28731629680976154924040067)
        ·
          refine ⟨43097444521464232386060101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28731629680976154924040067 43097444521464232386060101)
          ·
            refine ⟨8080770847774543572386269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43097444521464232386060101 8080770847774543572386269)
            ·
              refine ⟨3030289067915453839644851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8080770847774543572386269 3030289067915453839644851)
              ·
                refine ⟨4545433601873180759467277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3030289067915453839644851 4545433601873180759467277)
                ·
                  refine ⟨1704537600702442784800229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4545433601873180759467277 1704537600702442784800229)
                  ·
                    refine ⟨319600800131708022150043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1704537600702442784800229 319600800131708022150043)
                    ·
                      rfl

theorem cell23_1867261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 1, 3, 4].length) (baseStart_1867261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1867261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1867261 prefixEnd_1867261 := by exact prefixLift 1867261
  have htrace : WordTrace (prefixWord ++ tailWord_1867261) baseStart_1867261 baseEnd_1867261 := by
    simpa [prefixWord, tailWord_1867261, baseEnd_1867261] using wordTrace_append hprefix tailTrace_1867261
  have hstable : (prefixWord ++ tailWord_1867261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867261).length < 2 ^ (prefixWord ++ tailWord_1867261).sum := by decide
  have hdescent : baseEnd_1867261 < baseStart_1867261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867288 : List Nat := [2, 1, 2, 3, 4, 1, 2, 1, 2, 2, 3]
def baseStart_1867288 : Nat := 118140960795 + 1867288 * 2 ^ 59
def prefixEnd_1867288 : Nat := 4983230072969 + 3 ^ 40 * 1867288 * 2
def baseEnd_1867288 : Nat := 958816264372795460812505

theorem tailTrace_1867288 : CollatzResearch.WordTrace tailWord_1867288 prefixEnd_1867288 958816264372795460812505 := by
  unfold tailWord_1867288
  simp only [CollatzResearch.WordTrace]
  refine ⟨34052794229570979122997259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45403725639427972163996345 34052794229570979122997259)
  ·
    refine ⟨51079191344356468684495889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34052794229570979122997259 51079191344356468684495889)
    ·
      refine ⟨38309393508267351513371917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51079191344356468684495889 38309393508267351513371917)
      ·
        refine ⟨14366022565600256817514469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38309393508267351513371917 14366022565600256817514469)
        ·
          refine ⟨2693629231050048153283963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14366022565600256817514469 2693629231050048153283963)
          ·
            refine ⟨4040443846575072229925945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2693629231050048153283963 4040443846575072229925945)
            ·
              refine ⟨3030332884931304172444459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4040443846575072229925945 3030332884931304172444459)
              ·
                refine ⟨4545499327396956258666689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3030332884931304172444459 4545499327396956258666689)
                ·
                  refine ⟨3409124495547717194000017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4545499327396956258666689 3409124495547717194000017)
                  ·
                    refine ⟨2556843371660787895500013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3409124495547717194000017 2556843371660787895500013)
                    ·
                      refine ⟨958816264372795460812505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2556843371660787895500013 958816264372795460812505)
                      ·
                        rfl

theorem cell23_1867288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_1867288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1867288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1867288 prefixEnd_1867288 := by exact prefixLift 1867288
  have htrace : WordTrace (prefixWord ++ tailWord_1867288) baseStart_1867288 baseEnd_1867288 := by
    simpa [prefixWord, tailWord_1867288, baseEnd_1867288] using wordTrace_append hprefix tailTrace_1867288
  have hstable : (prefixWord ++ tailWord_1867288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867288).length < 2 ^ (prefixWord ++ tailWord_1867288).sum := by decide
  have hdescent : baseEnd_1867288 < baseStart_1867288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867364 : List Nat := [2, 3, 1, 1, 2, 4, 10]
def baseStart_1867364 : Nat := 118140960795 + 1867364 * 2 ^ 59
def prefixEnd_1867364 : Nat := 4983230072969 + 3 ^ 40 * 1867364 * 2
def baseEnd_1867364 : Nat := 11837719616080705721755

theorem tailTrace_1867364 : CollatzResearch.WordTrace tailWord_1867364 prefixEnd_1867364 11837719616080705721755 := by
  unfold tailWord_1867364
  simp only [CollatzResearch.WordTrace]
  refine ⟨34054180203433311612880573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45405573604577748817174097 34054180203433311612880573)
  ·
    refine ⟨12770317576287491854830215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34054180203433311612880573 12770317576287491854830215)
    ·
      refine ⟨19155476364431237782245323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12770317576287491854830215 19155476364431237782245323)
      ·
        refine ⟨28733214546646856673367985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19155476364431237782245323 28733214546646856673367985)
        ·
          refine ⟨21549910909985142505025989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28733214546646856673367985 21549910909985142505025989)
          ·
            refine ⟨4040608295622214219692373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21549910909985142505025989 4040608295622214219692373)
            ·
              refine ⟨11837719616080705721755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4040608295622214219692373 11837719616080705721755)
              ·
                rfl

theorem cell23_1867364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 10].length) (baseStart_1867364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1867364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1867364 prefixEnd_1867364 := by exact prefixLift 1867364
  have htrace : WordTrace (prefixWord ++ tailWord_1867364) baseStart_1867364 baseEnd_1867364 := by
    simpa [prefixWord, tailWord_1867364, baseEnd_1867364] using wordTrace_append hprefix tailTrace_1867364
  have hstable : (prefixWord ++ tailWord_1867364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867364).length < 2 ^ (prefixWord ++ tailWord_1867364).sum := by decide
  have hdescent : baseEnd_1867364 < baseStart_1867364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867368 : List Nat := [2, 1, 4, 3, 1, 2, 1, 1, 4, 4]
def baseStart_1867368 : Nat := 118140960795 + 1867368 * 2 ^ 59
def prefixEnd_1867368 : Nat := 4983230072969 + 3 ^ 40 * 1867368 * 2
def baseEnd_1867368 : Nat := 319619114275051715937379

theorem tailTrace_1867368 : CollatzResearch.WordTrace tailWord_1867368 prefixEnd_1867368 319619114275051715937379 := by
  unfold tailWord_1867368
  simp only [CollatzResearch.WordTrace]
  refine ⟨34054253149426065954453379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45405670865901421272604505 34054253149426065954453379)
  ·
    refine ⟨51081379724139098931680069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34054253149426065954453379 51081379724139098931680069)
    ·
      refine ⟨9577758698276081049690013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51081379724139098931680069 9577758698276081049690013)
      ·
        refine ⟨3591659511853530393633755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9577758698276081049690013 3591659511853530393633755)
        ·
          refine ⟨5387489267780295590450633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3591659511853530393633755 5387489267780295590450633)
          ·
            refine ⟨4040616950835221692837975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5387489267780295590450633 4040616950835221692837975)
            ·
              refine ⟨6060925426252832539256963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4040616950835221692837975 6060925426252832539256963)
              ·
                refine ⟨9091388139379248808885445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6060925426252832539256963 9091388139379248808885445)
                ·
                  refine ⟨1704635276133609151666021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9091388139379248808885445 1704635276133609151666021)
                  ·
                    refine ⟨319619114275051715937379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1704635276133609151666021 319619114275051715937379)
                    ·
                      rfl

theorem cell23_1867368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_1867368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1867368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1867368 prefixEnd_1867368 := by exact prefixLift 1867368
  have htrace : WordTrace (prefixWord ++ tailWord_1867368) baseStart_1867368 baseEnd_1867368 := by
    simpa [prefixWord, tailWord_1867368, baseEnd_1867368] using wordTrace_append hprefix tailTrace_1867368
  have hstable : (prefixWord ++ tailWord_1867368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867368).length < 2 ^ (prefixWord ++ tailWord_1867368).sum := by decide
  have hdescent : baseEnd_1867368 < baseStart_1867368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867404 : List Nat := [2, 2, 1, 2, 1, 1, 3, 1, 1, 4, 5]
def baseStart_1867404 : Nat := 118140960795 + 1867404 * 2 ^ 59
def prefixEnd_1867404 : Nat := 4983230072969 + 3 ^ 40 * 1867404 * 2
def baseEnd_1867404 : Nat := 958875828128717006961971

theorem tailTrace_1867404 : CollatzResearch.WordTrace tailWord_1867404 prefixEnd_1867404 958875828128717006961971 := by
  unfold tailWord_1867404
  simp only [CollatzResearch.WordTrace]
  refine ⟨34054909663360855028608633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45406546217814473371478177 34054909663360855028608633)
  ·
    refine ⟨25541182247520641271456475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34054909663360855028608633 25541182247520641271456475)
    ·
      refine ⟨38311773371280961907184713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25541182247520641271456475 38311773371280961907184713)
      ·
        refine ⟨28733830028460721430388535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38311773371280961907184713 28733830028460721430388535)
        ·
          refine ⟨43100745042691082145582803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28733830028460721430388535 43100745042691082145582803)
          ·
            refine ⟨64651117564036623218374205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43100745042691082145582803 64651117564036623218374205)
            ·
              refine ⟨24244169086513733706890327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64651117564036623218374205 24244169086513733706890327)
              ·
                refine ⟨36366253629770600560335491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24244169086513733706890327 36366253629770600560335491)
                ·
                  refine ⟨54549380444655900840503237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36366253629770600560335491 54549380444655900840503237)
                  ·
                    refine ⟨10228008833372981407594357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54549380444655900840503237 10228008833372981407594357)
                    ·
                      refine ⟨958875828128717006961971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10228008833372981407594357 958875828128717006961971)
                      ·
                        rfl

theorem cell23_1867404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_1867404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1867404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1867404 prefixEnd_1867404 := by exact prefixLift 1867404
  have htrace : WordTrace (prefixWord ++ tailWord_1867404) baseStart_1867404 baseEnd_1867404 := by
    simpa [prefixWord, tailWord_1867404, baseEnd_1867404] using wordTrace_append hprefix tailTrace_1867404
  have hstable : (prefixWord ++ tailWord_1867404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867404).length < 2 ^ (prefixWord ++ tailWord_1867404).sum := by decide
  have hdescent : baseEnd_1867404 < baseStart_1867404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867426 : List Nat := [3, 3, 1, 4, 2, 1, 1, 1, 3, 2, 2]
def baseStart_1867426 : Nat := 118140960795 + 1867426 * 2 ^ 59
def prefixEnd_1867426 : Nat := 4983230072969 + 3 ^ 40 * 1867426 * 2
def baseEnd_1867426 : Nat := 958887124703115920886871

theorem tailTrace_1867426 : CollatzResearch.WordTrace tailWord_1867426 prefixEnd_1867426 958887124703115920886871 := by
  unfold tailWord_1867426
  simp only [CollatzResearch.WordTrace]
  refine ⟨17027655433160501953629533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45407081155094671876345421 17027655433160501953629533)
  ·
    refine ⟨6385370787435188232611075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17027655433160501953629533 6385370787435188232611075)
    ·
      refine ⟨9578056181152782348916613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6385370787435188232611075 9578056181152782348916613)
      ·
        refine ⟨1795885533966146690421865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9578056181152782348916613 1795885533966146690421865)
        ·
          refine ⟨1346914150474610017816399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1795885533966146690421865 1346914150474610017816399)
          ·
            refine ⟨2020371225711915026724599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1346914150474610017816399 2020371225711915026724599)
            ·
              refine ⟨3030556838567872540086899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2020371225711915026724599 3030556838567872540086899)
              ·
                refine ⟨4545835257851808810130349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3030556838567872540086899 4545835257851808810130349)
                ·
                  refine ⟨1704688221694428303798881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4545835257851808810130349 1704688221694428303798881)
                  ·
                    refine ⟨1278516166270821227849161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1704688221694428303798881 1278516166270821227849161)
                    ·
                      refine ⟨958887124703115920886871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1278516166270821227849161 958887124703115920886871)
                      ·
                        rfl

theorem cell23_1867426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_1867426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1867426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1867426 prefixEnd_1867426 := by exact prefixLift 1867426
  have htrace : WordTrace (prefixWord ++ tailWord_1867426) baseStart_1867426 baseEnd_1867426 := by
    simpa [prefixWord, tailWord_1867426, baseEnd_1867426] using wordTrace_append hprefix tailTrace_1867426
  have hstable : (prefixWord ++ tailWord_1867426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867426).length < 2 ^ (prefixWord ++ tailWord_1867426).sum := by decide
  have hdescent : baseEnd_1867426 < baseStart_1867426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867452 : List Nat := [2, 2, 2, 3, 1, 4, 1, 2, 1, 3, 2]
def baseStart_1867452 : Nat := 118140960795 + 1867452 * 2 ^ 59
def prefixEnd_1867452 : Nat := 4983230072969 + 3 ^ 40 * 1867452 * 2
def baseEnd_1867452 : Nat := 958900475200132819161751

theorem tailTrace_1867452 : CollatzResearch.WordTrace tailWord_1867452 prefixEnd_1867452 958900475200132819161751 := by
  unfold tailWord_1867452
  simp only [CollatzResearch.WordTrace]
  refine ⟨34055785015273907127482305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45407713353698542836643073 34055785015273907127482305)
  ·
    refine ⟨25541838761455430345611729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34055785015273907127482305 25541838761455430345611729)
    ·
      refine ⟨19156379071091572759208797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25541838761455430345611729 19156379071091572759208797)
      ·
        refine ⟨7183642151659339784703299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19156379071091572759208797 7183642151659339784703299)
        ·
          refine ⟨10775463227489009677054949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7183642151659339784703299 10775463227489009677054949)
          ·
            refine ⟨2020399355154189314447803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10775463227489009677054949 2020399355154189314447803)
            ·
              refine ⟨3030599032731283971671705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2020399355154189314447803 3030599032731283971671705)
              ·
                refine ⟨2272949274548462978753779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3030599032731283971671705 2272949274548462978753779)
                ·
                  refine ⟨3409423911822694468130669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2272949274548462978753779 3409423911822694468130669)
                  ·
                    refine ⟨1278533966933510425549001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3409423911822694468130669 1278533966933510425549001)
                    ·
                      refine ⟨958900475200132819161751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1278533966933510425549001 958900475200132819161751)
                      ·
                        rfl

theorem cell23_1867452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_1867452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1867452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1867452 prefixEnd_1867452 := by exact prefixLift 1867452
  have htrace : WordTrace (prefixWord ++ tailWord_1867452) baseStart_1867452 baseEnd_1867452 := by
    simpa [prefixWord, tailWord_1867452, baseEnd_1867452] using wordTrace_append hprefix tailTrace_1867452
  have hstable : (prefixWord ++ tailWord_1867452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867452).length < 2 ^ (prefixWord ++ tailWord_1867452).sum := by decide
  have hdescent : baseEnd_1867452 < baseStart_1867452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867482 : List Nat := [3, 1, 1, 2, 2, 4, 2, 2, 2, 2, 2]
def baseStart_1867482 : Nat := 118140960795 + 1867482 * 2 ^ 59
def prefixEnd_1867482 : Nat := 4983230072969 + 3 ^ 40 * 1867482 * 2
def baseEnd_1867482 : Nat := 958915879619767701786613

theorem tailTrace_1867482 : CollatzResearch.WordTrace tailWord_1867482 prefixEnd_1867482 958915879619767701786613 := by
  unfold tailWord_1867482
  simp only [CollatzResearch.WordTrace]
  refine ⟨17028166055109782344639175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45408442813626086252371133 17028166055109782344639175)
  ·
    refine ⟨25542249082664673516958763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17028166055109782344639175 25542249082664673516958763)
    ·
      refine ⟨38313373623997010275438145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25542249082664673516958763 38313373623997010275438145)
      ·
        refine ⟨28735030217997757706578609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38313373623997010275438145 28735030217997757706578609)
        ·
          refine ⟨21551272663498318279933957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28735030217997757706578609 21551272663498318279933957)
          ·
            refine ⟨4040863624405934677487617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21551272663498318279933957 4040863624405934677487617)
            ·
              refine ⟨3030647718304451008115713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4040863624405934677487617 3030647718304451008115713)
              ·
                refine ⟨2272985788728338256086785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3030647718304451008115713 2272985788728338256086785)
                ·
                  refine ⟨1704739341546253692065089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2272985788728338256086785 1704739341546253692065089)
                  ·
                    refine ⟨1278554506159690269048817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1704739341546253692065089 1278554506159690269048817)
                    ·
                      refine ⟨958915879619767701786613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1278554506159690269048817 958915879619767701786613)
                      ·
                        rfl

theorem cell23_1867482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 2, 2, 2, 2].length) (baseStart_1867482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1867482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1867482 prefixEnd_1867482 := by exact prefixLift 1867482
  have htrace : WordTrace (prefixWord ++ tailWord_1867482) baseStart_1867482 baseEnd_1867482 := by
    simpa [prefixWord, tailWord_1867482, baseEnd_1867482] using wordTrace_append hprefix tailTrace_1867482
  have hstable : (prefixWord ++ tailWord_1867482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867482).length < 2 ^ (prefixWord ++ tailWord_1867482).sum := by decide
  have hdescent : baseEnd_1867482 < baseStart_1867482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867495 : List Nat := [1, 1, 5, 4, 1, 1, 1, 1, 2, 2, 4]
def baseStart_1867495 : Nat := 118140960795 + 1867495 * 2 ^ 59
def prefixEnd_1867495 : Nat := 4983230072969 + 3 ^ 40 * 1867495 * 2
def baseEnd_1867495 : Nat := 958922554868276150924053

theorem tailTrace_1867495 : CollatzResearch.WordTrace tailWord_1867495 prefixEnd_1867495 958922554868276150924053 := by
  unfold tailWord_1867495
  simp only [CollatzResearch.WordTrace]
  refine ⟨68113138369392032598779939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45408758912928021732519959 68113138369392032598779939)
  ·
    refine ⟨102169707554088048898169909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68113138369392032598779939 102169707554088048898169909)
    ·
      refine ⟨9578410083195754584203429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102169707554088048898169909 9578410083195754584203429)
      ·
        refine ⟨1795951890599203984538143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9578410083195754584203429 1795951890599203984538143)
        ·
          refine ⟨2693927835898805976807215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1795951890599203984538143 2693927835898805976807215)
          ·
            refine ⟨4040891753848208965210823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2693927835898805976807215 4040891753848208965210823)
            ·
              refine ⟨6061337630772313447816235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4040891753848208965210823 6061337630772313447816235)
              ·
                refine ⟨9092006446158470171724353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6061337630772313447816235 9092006446158470171724353)
                ·
                  refine ⟨6819004834618852628793265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9092006446158470171724353 6819004834618852628793265)
                  ·
                    refine ⟨5114253625964139471594949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6819004834618852628793265 5114253625964139471594949)
                    ·
                      refine ⟨958922554868276150924053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5114253625964139471594949 958922554868276150924053)
                      ·
                        rfl

theorem cell23_1867495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_1867495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1867495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1867495 prefixEnd_1867495 := by exact prefixLift 1867495
  have htrace : WordTrace (prefixWord ++ tailWord_1867495) baseStart_1867495 baseEnd_1867495 := by
    simpa [prefixWord, tailWord_1867495, baseEnd_1867495] using wordTrace_append hprefix tailTrace_1867495
  have hstable : (prefixWord ++ tailWord_1867495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867495).length < 2 ^ (prefixWord ++ tailWord_1867495).sum := by decide
  have hdescent : baseEnd_1867495 < baseStart_1867495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867533 : List Nat := [1, 7, 2, 1, 1, 1, 1, 1, 4, 2, 2]
def baseStart_1867533 : Nat := 118140960795 + 1867533 * 2 ^ 59
def prefixEnd_1867533 : Nat := 4983230072969 + 3 ^ 40 * 1867533 * 2
def baseEnd_1867533 : Nat := 958942067133147002248879

theorem tailTrace_1867533 : CollatzResearch.WordTrace tailWord_1867533 prefixEnd_1867533 958942067133147002248879 := by
  unfold tailWord_1867533
  simp only [CollatzResearch.WordTrace]
  refine ⟨68114524343254365088663253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45409682895502910059108835 68114524343254365088663253)
  ·
    refine ⟨1596434164295024181765545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 68114524343254365088663253 1596434164295024181765545)
    ·
      refine ⟨1197325623221268136324159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1596434164295024181765545 1197325623221268136324159)
      ·
        refine ⟨1795988434831902204486239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1197325623221268136324159 1795988434831902204486239)
        ·
          refine ⟨2693982652247853306729359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1795988434831902204486239 2693982652247853306729359)
          ·
            refine ⟨4040973978371779960094039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2693982652247853306729359 4040973978371779960094039)
            ·
              refine ⟨6061460967557669940141059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4040973978371779960094039 6061460967557669940141059)
              ·
                refine ⟨9092191451336504910211589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6061460967557669940141059 9092191451336504910211589)
                ·
                  refine ⟨1704785897125594670664673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9092191451336504910211589 1704785897125594670664673)
                  ·
                    refine ⟨1278589422844196002998505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1704785897125594670664673 1278589422844196002998505)
                    ·
                      refine ⟨958942067133147002248879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1278589422844196002998505 958942067133147002248879)
                      ·
                        rfl

theorem cell23_1867533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_1867533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1867533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1867533 prefixEnd_1867533 := by exact prefixLift 1867533
  have htrace : WordTrace (prefixWord ++ tailWord_1867533) baseStart_1867533 baseEnd_1867533 := by
    simpa [prefixWord, tailWord_1867533, baseEnd_1867533] using wordTrace_append hprefix tailTrace_1867533
  have hstable : (prefixWord ++ tailWord_1867533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867533).length < 2 ^ (prefixWord ++ tailWord_1867533).sum := by decide
  have hdescent : baseEnd_1867533 < baseStart_1867533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867551 : List Nat := [1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 6]
def baseStart_1867551 : Nat := 118140960795 + 1867551 * 2 ^ 59
def prefixEnd_1867551 : Nat := 4983230072969 + 3 ^ 40 * 1867551 * 2
def baseEnd_1867551 : Nat := 958951309784927931823795

theorem tailTrace_1867551 : CollatzResearch.WordTrace tailWord_1867551 prefixEnd_1867551 958951309784927931823795 := by
  unfold tailWord_1867551
  simp only [CollatzResearch.WordTrace]
  refine ⟨68115180857189154162818507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45410120571459436108545671 68115180857189154162818507)
  ·
    refine ⟨102172771285783731244227761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68115180857189154162818507 102172771285783731244227761)
    ·
      refine ⟨76629578464337798433170821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102172771285783731244227761 76629578464337798433170821)
      ·
        refine ⟨14368045962063337206219529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76629578464337798433170821 14368045962063337206219529)
        ·
          refine ⟨10776034471547502904664647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14368045962063337206219529 10776034471547502904664647)
          ·
            refine ⟨16164051707321254356996971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10776034471547502904664647 16164051707321254356996971)
            ·
              refine ⟨24246077560981881535495457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16164051707321254356996971 24246077560981881535495457)
              ·
                refine ⟨18184558170736411151621593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24246077560981881535495457 18184558170736411151621593)
                ·
                  refine ⟨13638418628052308363716195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18184558170736411151621593 13638418628052308363716195)
                  ·
                    refine ⟨20457627942078462545574293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13638418628052308363716195 20457627942078462545574293)
                    ·
                      refine ⟨958951309784927931823795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20457627942078462545574293 958951309784927931823795)
                      ·
                        rfl

theorem cell23_1867551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_1867551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1867551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1867551 prefixEnd_1867551 := by exact prefixLift 1867551
  have htrace : WordTrace (prefixWord ++ tailWord_1867551) baseStart_1867551 baseEnd_1867551 := by
    simpa [prefixWord, tailWord_1867551, baseEnd_1867551] using wordTrace_append hprefix tailTrace_1867551
  have hstable : (prefixWord ++ tailWord_1867551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867551).length < 2 ^ (prefixWord ++ tailWord_1867551).sum := by decide
  have hdescent : baseEnd_1867551 < baseStart_1867551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867631 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 2, 5, 5]
def baseStart_1867631 : Nat := 118140960795 + 1867631 * 2 ^ 59
def prefixEnd_1867631 : Nat := 4983230072969 + 3 ^ 40 * 1867631 * 2
def baseEnd_1867631 : Nat := 958992388237287618823427

theorem tailTrace_1867631 : CollatzResearch.WordTrace tailWord_1867631 prefixEnd_1867631 958992388237287618823427 := by
  unfold tailWord_1867631
  simp only [CollatzResearch.WordTrace]
  refine ⟨68118098696899327825730747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45412065797932885217153831 68118098696899327825730747)
  ·
    refine ⟨102177148045348991738596121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68118098696899327825730747 102177148045348991738596121)
    ·
      refine ⟨76632861034011743803947091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102177148045348991738596121 76632861034011743803947091)
      ·
        refine ⟨114949291551017615705920637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76632861034011743803947091 114949291551017615705920637)
        ·
          refine ⟨43105984331631605889720239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114949291551017615705920637 43105984331631605889720239)
          ·
            refine ⟨64658976497447408834580359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43105984331631605889720239 64658976497447408834580359)
            ·
              refine ⟨96988464746171113251870539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64658976497447408834580359 96988464746171113251870539)
              ·
                refine ⟨145482697119256669877805809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96988464746171113251870539 145482697119256669877805809)
                ·
                  refine ⟨109112022839442502408354357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145482697119256669877805809 109112022839442502408354357)
                  ·
                    refine ⟨10229252141197734600783221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 109112022839442502408354357 10229252141197734600783221)
                    ·
                      refine ⟨958992388237287618823427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10229252141197734600783221 958992388237287618823427)
                      ·
                        rfl

theorem cell23_1867631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5, 5].length) (baseStart_1867631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1867631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1867631 prefixEnd_1867631 := by exact prefixLift 1867631
  have htrace : WordTrace (prefixWord ++ tailWord_1867631) baseStart_1867631 baseEnd_1867631 := by
    simpa [prefixWord, tailWord_1867631, baseEnd_1867631] using wordTrace_append hprefix tailTrace_1867631
  have hstable : (prefixWord ++ tailWord_1867631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867631).length < 2 ^ (prefixWord ++ tailWord_1867631).sum := by decide
  have hdescent : baseEnd_1867631 < baseStart_1867631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867651 : List Nat := [1, 1, 1, 3, 4, 13]
def baseStart_1867651 : Nat := 118140960795 + 1867651 * 2 ^ 59
def prefixEnd_1867651 : Nat := 4983230072969 + 3 ^ 40 * 1867651 * 2
def baseEnd_1867651 : Nat := 3946512995269043376845

theorem tailTrace_1867651 : CollatzResearch.WordTrace tailWord_1867651 prefixEnd_1867651 3946512995269043376845 := by
  unfold tailWord_1867651
  simp only [CollatzResearch.WordTrace]
  refine ⟨68118828156826871241458807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45412552104551247494305871 68118828156826871241458807)
  ·
    refine ⟨102178242235240306862188211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68118828156826871241458807 102178242235240306862188211)
    ·
      refine ⟨153267363352860460293282317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102178242235240306862188211 153267363352860460293282317)
      ·
        refine ⟨57475261257322672609980869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153267363352860460293282317 57475261257322672609980869)
        ·
          refine ⟨10776611485748001114371413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57475261257322672609980869 10776611485748001114371413)
          ·
            refine ⟨3946512995269043376845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 10776611485748001114371413 3946512995269043376845)
            ·
              rfl

theorem cell23_1867651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 13].length) (baseStart_1867651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1867651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1867651 prefixEnd_1867651 := by exact prefixLift 1867651
  have htrace : WordTrace (prefixWord ++ tailWord_1867651) baseStart_1867651 baseEnd_1867651 := by
    simpa [prefixWord, tailWord_1867651, baseEnd_1867651] using wordTrace_append hprefix tailTrace_1867651
  have hstable : (prefixWord ++ tailWord_1867651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867651).length < 2 ^ (prefixWord ++ tailWord_1867651).sum := by decide
  have hdescent : baseEnd_1867651 < baseStart_1867651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867672 : List Nat := [2, 1, 2, 6, 1, 1, 2, 1, 1, 6]
def baseStart_1867672 : Nat := 118140960795 + 1867672 * 2 ^ 59
def prefixEnd_1867672 : Nat := 4983230072969 + 3 ^ 40 * 1867672 * 2
def baseEnd_1867672 : Nat := 319671146981373986136913

theorem tailTrace_1867672 : CollatzResearch.WordTrace tailWord_1867672 prefixEnd_1867672 319671146981373986136913 := by
  unfold tailWord_1867672
  simp only [CollatzResearch.WordTrace]
  refine ⟨34059797044875395913986635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45413062726500527885315513 34059797044875395913986635)
  ·
    refine ⟨51089695567313093870979953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34059797044875395913986635 51089695567313093870979953)
    ·
      refine ⟨38317271675484820403234965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51089695567313093870979953 38317271675484820403234965)
      ·
        refine ⟨1796122109788350956401639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 38317271675484820403234965 1796122109788350956401639)
        ·
          refine ⟨2694183164682526434602459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1796122109788350956401639 2694183164682526434602459)
          ·
            refine ⟨4041274747023789651903689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2694183164682526434602459 4041274747023789651903689)
            ·
              refine ⟨3030956060267842238927767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4041274747023789651903689 3030956060267842238927767)
              ·
                refine ⟨4546434090401763358391651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3030956060267842238927767 4546434090401763358391651)
                ·
                  refine ⟨6819651135602645037587477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4546434090401763358391651 6819651135602645037587477)
                  ·
                    refine ⟨319671146981373986136913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6819651135602645037587477 319671146981373986136913)
                    ·
                      rfl

theorem cell23_1867672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 1, 1, 6].length) (baseStart_1867672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1867672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1867672 prefixEnd_1867672 := by exact prefixLift 1867672
  have htrace : WordTrace (prefixWord ++ tailWord_1867672) baseStart_1867672 baseEnd_1867672 := by
    simpa [prefixWord, tailWord_1867672, baseEnd_1867672] using wordTrace_append hprefix tailTrace_1867672
  have hstable : (prefixWord ++ tailWord_1867672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867672).length < 2 ^ (prefixWord ++ tailWord_1867672).sum := by decide
  have hdescent : baseEnd_1867672 < baseStart_1867672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867679 : List Nat := [1, 1, 2, 5, 3, 1, 1, 2, 3, 2, 2]
def baseStart_1867679 : Nat := 118140960795 + 1867679 * 2 ^ 59
def prefixEnd_1867679 : Nat := 4983230072969 + 3 ^ 40 * 1867679 * 2
def baseEnd_1867679 : Nat := 959017035308703431023207

theorem tailTrace_1867679 : CollatzResearch.WordTrace tailWord_1867679 prefixEnd_1867679 959017035308703431023207 := by
  unfold tailWord_1867679
  simp only [CollatzResearch.WordTrace]
  refine ⟨68119849400725432023478091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45413232933816954682318727 68119849400725432023478091)
  ·
    refine ⟨102179774101088148035217137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68119849400725432023478091 102179774101088148035217137)
    ·
      refine ⟨76634830575816111026412853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102179774101088148035217137 76634830575816111026412853)
      ·
        refine ⟨7184515366482760408726205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76634830575816111026412853 7184515366482760408726205)
        ·
          refine ⟨2694193262431035153272327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7184515366482760408726205 2694193262431035153272327)
          ·
            refine ⟨4041289893646552729908491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2694193262431035153272327 4041289893646552729908491)
            ·
              refine ⟨6061934840469829094862737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4041289893646552729908491 6061934840469829094862737)
              ·
                refine ⟨4546451130352371821147053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6061934840469829094862737 4546451130352371821147053)
                ·
                  refine ⟨1704919173882139432930145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4546451130352371821147053 1704919173882139432930145)
                  ·
                    refine ⟨1278689380411604574697609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1704919173882139432930145 1278689380411604574697609)
                    ·
                      refine ⟨959017035308703431023207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1278689380411604574697609 959017035308703431023207)
                      ·
                        rfl

theorem cell23_1867679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_1867679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1867679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1867679 prefixEnd_1867679 := by exact prefixLift 1867679
  have htrace : WordTrace (prefixWord ++ tailWord_1867679) baseStart_1867679 baseEnd_1867679 := by
    simpa [prefixWord, tailWord_1867679, baseEnd_1867679] using wordTrace_append hprefix tailTrace_1867679
  have hstable : (prefixWord ++ tailWord_1867679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867679).length < 2 ^ (prefixWord ++ tailWord_1867679).sum := by decide
  have hdescent : baseEnd_1867679 < baseStart_1867679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867695 : List Nat := [1, 1, 2, 1, 2, 2, 4, 2, 4, 1, 3]
def baseStart_1867695 : Nat := 118140960795 + 1867695 * 2 ^ 59
def prefixEnd_1867695 : Nat := 4983230072969 + 3 ^ 40 * 1867695 * 2
def baseEnd_1867695 : Nat := 959025250999175368423133

theorem tailTrace_1867695 : CollatzResearch.WordTrace tailWord_1867695 prefixEnd_1867695 959025250999175368423133 := by
  unfold tailWord_1867695
  simp only [CollatzResearch.WordTrace]
  refine ⟨68120432968667466756060539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45413621979111644504040359 68120432968667466756060539)
  ·
    refine ⟨102180649453001200134090809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68120432968667466756060539 102180649453001200134090809)
    ·
      refine ⟨76635487089750900100568107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102180649453001200134090809 76635487089750900100568107)
      ·
        refine ⟨114953230634626350150852161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76635487089750900100568107 114953230634626350150852161)
        ·
          refine ⟨86214922975969762613139121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114953230634626350150852161 86214922975969762613139121)
          ·
            refine ⟨64661192231977321959854341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86214922975969762613139121 64661192231977321959854341)
            ·
              refine ⟨12123973543495747867472689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64661192231977321959854341 12123973543495747867472689)
              ·
                refine ⟨9092980157621810900604517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12123973543495747867472689 9092980157621810900604517)
                ·
                  refine ⟨1704933779554089543863347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9092980157621810900604517 1704933779554089543863347)
                  ·
                    refine ⟨2557400669331134315795021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1704933779554089543863347 2557400669331134315795021)
                    ·
                      refine ⟨959025250999175368423133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2557400669331134315795021 959025250999175368423133)
                      ·
                        rfl

theorem cell23_1867695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 4, 1, 3].length) (baseStart_1867695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1867695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1867695 prefixEnd_1867695 := by exact prefixLift 1867695
  have htrace : WordTrace (prefixWord ++ tailWord_1867695) baseStart_1867695 baseEnd_1867695 := by
    simpa [prefixWord, tailWord_1867695, baseEnd_1867695] using wordTrace_append hprefix tailTrace_1867695
  have hstable : (prefixWord ++ tailWord_1867695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867695).length < 2 ^ (prefixWord ++ tailWord_1867695).sum := by decide
  have hdescent : baseEnd_1867695 < baseStart_1867695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867728 : List Nat := [2, 1, 1, 1, 1, 2, 6, 1, 2, 6]
def baseStart_1867728 : Nat := 118140960795 + 1867728 * 2 ^ 59
def prefixEnd_1867728 : Nat := 4983230072969 + 3 ^ 40 * 1867728 * 2
def baseEnd_1867728 : Nat := 319680731953591246436827

theorem tailTrace_1867728 : CollatzResearch.WordTrace tailWord_1867728 prefixEnd_1867728 319680731953591246436827 := by
  unfold tailWord_1867728
  simp only [CollatzResearch.WordTrace]
  refine ⟨34060818288773956696005919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45414424385031942261341225 34060818288773956696005919)
  ·
    refine ⟨51091227433160935044008879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34060818288773956696005919 51091227433160935044008879)
    ·
      refine ⟨76636841149741402566013319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51091227433160935044008879 76636841149741402566013319)
      ·
        refine ⟨114955261724612103849019979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76636841149741402566013319 114955261724612103849019979)
        ·
          refine ⟨172432892586918155773529969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114955261724612103849019979 172432892586918155773529969)
          ·
            refine ⟨129324669440188616830147477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172432892586918155773529969 129324669440188616830147477)
            ·
              refine ⟨6062093880008841413913163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 129324669440188616830147477 6062093880008841413913163)
              ·
                refine ⟨9093140820013262120869745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6062093880008841413913163 9093140820013262120869745)
                ·
                  refine ⟨6819855615009946590652309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9093140820013262120869745 6819855615009946590652309)
                  ·
                    refine ⟨319680731953591246436827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6819855615009946590652309 319680731953591246436827)
                    ·
                      rfl

theorem cell23_1867728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 2, 6].length) (baseStart_1867728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1867728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1867728 prefixEnd_1867728 := by exact prefixLift 1867728
  have htrace : WordTrace (prefixWord ++ tailWord_1867728) baseStart_1867728 baseEnd_1867728 := by
    simpa [prefixWord, tailWord_1867728, baseEnd_1867728] using wordTrace_append hprefix tailTrace_1867728
  have hstable : (prefixWord ++ tailWord_1867728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867728).length < 2 ^ (prefixWord ++ tailWord_1867728).sum := by decide
  have hdescent : baseEnd_1867728 < baseStart_1867728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867775 : List Nat := [1, 1, 2, 2, 1, 2, 1, 8, 5]
def baseStart_1867775 : Nat := 118140960795 + 1867775 * 2 ^ 59
def prefixEnd_1867775 : Nat := 4983230072969 + 3 ^ 40 * 1867775 * 2
def baseEnd_1867775 : Nat := 106562925494615006158085

theorem tailTrace_1867775 : CollatzResearch.WordTrace tailWord_1867775 prefixEnd_1867775 106562925494615006158085 := by
  unfold tailWord_1867775
  simp only [CollatzResearch.WordTrace]
  refine ⟨68123350808377640418972779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45415567205585093612648519 68123350808377640418972779)
  ·
    refine ⟨102185026212566460628459169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68123350808377640418972779 102185026212566460628459169)
    ·
      refine ⟨76638769659424845471344377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102185026212566460628459169 76638769659424845471344377)
      ·
        refine ⟨57479077244568634103508283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76638769659424845471344377 57479077244568634103508283)
        ·
          refine ⟨86218615866852951155262425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57479077244568634103508283 86218615866852951155262425)
          ·
            refine ⟨64663961900139713366446819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86218615866852951155262425 64663961900139713366446819)
            ·
              refine ⟨96995942850209570049670229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64663961900139713366446819 96995942850209570049670229)
              ·
                refine ⟨1136671205275893399019573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 96995942850209570049670229 1136671205275893399019573)
                ·
                  refine ⟨106562925494615006158085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1136671205275893399019573 106562925494615006158085)
                  ·
                    rfl

theorem cell23_1867775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 8, 5].length) (baseStart_1867775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1867775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1867775 prefixEnd_1867775 := by exact prefixLift 1867775
  have htrace : WordTrace (prefixWord ++ tailWord_1867775) baseStart_1867775 baseEnd_1867775 := by
    simpa [prefixWord, tailWord_1867775, baseEnd_1867775] using wordTrace_append hprefix tailTrace_1867775
  have hstable : (prefixWord ++ tailWord_1867775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867775).length < 2 ^ (prefixWord ++ tailWord_1867775).sum := by decide
  have hdescent : baseEnd_1867775 < baseStart_1867775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867780 : List Nat := [2, 3, 2, 4, 2, 1, 2, 1, 2, 1, 3]
def baseStart_1867780 : Nat := 118140960795 + 1867780 * 2 ^ 59
def prefixEnd_1867780 : Nat := 4983230072969 + 3 ^ 40 * 1867780 * 2
def baseEnd_1867780 : Nat := 959068896854807535860243

theorem tailTrace_1867780 : CollatzResearch.WordTrace tailWord_1867780 prefixEnd_1867780 959068896854807535860243 := by
  unfold tailWord_1867780
  simp only [CollatzResearch.WordTrace]
  refine ⟨34061766586679763136452397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45415688782239684181936529 34061766586679763136452397)
  ·
    refine ⟨12773162470004911176169649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34061766586679763136452397 12773162470004911176169649)
    ·
      refine ⟨9579871852503683382127237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12773162470004911176169649 9579871852503683382127237)
      ·
        refine ⟨1796225972344440634148857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9579871852503683382127237 1796225972344440634148857)
        ·
          refine ⟨1347169479258330475611643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1796225972344440634148857 1347169479258330475611643)
          ·
            refine ⟨2020754218887495713417465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1347169479258330475611643 2020754218887495713417465)
            ·
              refine ⟨1515565664165621785063099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2020754218887495713417465 1515565664165621785063099)
              ·
                refine ⟨2273348496248432677594649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1515565664165621785063099 2273348496248432677594649)
                ·
                  refine ⟨1705011372186324508195987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2273348496248432677594649 1705011372186324508195987)
                  ·
                    refine ⟨2557517058279486762293981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1705011372186324508195987 2557517058279486762293981)
                    ·
                      refine ⟨959068896854807535860243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2557517058279486762293981 959068896854807535860243)
                      ·
                        rfl

theorem cell23_1867780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_1867780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1867780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1867780 prefixEnd_1867780 := by exact prefixLift 1867780
  have htrace : WordTrace (prefixWord ++ tailWord_1867780) baseStart_1867780 baseEnd_1867780 := by
    simpa [prefixWord, tailWord_1867780, baseEnd_1867780] using wordTrace_append hprefix tailTrace_1867780
  have hstable : (prefixWord ++ tailWord_1867780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867780).length < 2 ^ (prefixWord ++ tailWord_1867780).sum := by decide
  have hdescent : baseEnd_1867780 < baseStart_1867780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867786 : List Nat := [3, 1, 2, 2, 4, 1, 1, 3, 2, 2, 2]
def baseStart_1867786 : Nat := 118140960795 + 1867786 * 2 ^ 59
def prefixEnd_1867786 : Nat := 4983230072969 + 3 ^ 40 * 1867786 * 2
def baseEnd_1867786 : Nat := 959071977738734512385215

theorem tailTrace_1867786 : CollatzResearch.WordTrace tailWord_1867786 prefixEnd_1867786 959071977738734512385215 := by
  unfold tailWord_1867786
  simp only [CollatzResearch.WordTrace]
  refine ⟨17030938002834447324405803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45415834674225192865082141 17030938002834447324405803)
  ·
    refine ⟨25546407004251670986608705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17030938002834447324405803 25546407004251670986608705)
    ·
      refine ⟨19159805253188753239956529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25546407004251670986608705 19159805253188753239956529)
      ·
        refine ⟨14369853939891564929967397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19159805253188753239956529 14369853939891564929967397)
        ·
          refine ⟨2694347613729668424368887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14369853939891564929967397 2694347613729668424368887)
          ·
            refine ⟨4041521420594502636553331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2694347613729668424368887 4041521420594502636553331)
            ·
              refine ⟨6062282130891753954829997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4041521420594502636553331 6062282130891753954829997)
              ·
                refine ⟨2273355799084407733061249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6062282130891753954829997 2273355799084407733061249)
                ·
                  refine ⟨1705016849313305799795937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2273355799084407733061249 1705016849313305799795937)
                  ·
                    refine ⟨1278762636984979349846953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1705016849313305799795937 1278762636984979349846953)
                    ·
                      refine ⟨959071977738734512385215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1278762636984979349846953 959071977738734512385215)
                      ·
                        rfl

theorem cell23_1867786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 3, 2, 2, 2].length) (baseStart_1867786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1867786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1867786 prefixEnd_1867786 := by exact prefixLift 1867786
  have htrace : WordTrace (prefixWord ++ tailWord_1867786) baseStart_1867786 baseEnd_1867786 := by
    simpa [prefixWord, tailWord_1867786, baseEnd_1867786] using wordTrace_append hprefix tailTrace_1867786
  have hstable : (prefixWord ++ tailWord_1867786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867786).length < 2 ^ (prefixWord ++ tailWord_1867786).sum := by decide
  have hdescent : baseEnd_1867786 < baseStart_1867786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867822 : List Nat := [4, 1, 3, 1, 1, 2, 2, 2, 2, 5]
def baseStart_1867822 : Nat := 118140960795 + 1867822 * 2 ^ 59
def prefixEnd_1867822 : Nat := 4983230072969 + 3 ^ 40 * 1867822 * 2
def baseEnd_1867822 : Nat := 319696821014098790511683

theorem tailTrace_1867822 : CollatzResearch.WordTrace tailWord_1867822 prefixEnd_1867822 319696821014098790511683 := by
  unfold tailWord_1867822
  simp only [CollatzResearch.WordTrace]
  refine ⟨8515633129900920930741715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45416710026138244963955813 8515633129900920930741715)
  ·
    refine ⟨12773449694851381396112573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8515633129900920930741715 12773449694851381396112573)
    ·
      refine ⟨4790043635569268023542215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12773449694851381396112573 4790043635569268023542215)
      ·
        refine ⟨7185065453353902035313323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4790043635569268023542215 7185065453353902035313323)
        ·
          refine ⟨10777598180030853052969985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7185065453353902035313323 10777598180030853052969985)
          ·
            refine ⟨8083198635023139789727489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10777598180030853052969985 8083198635023139789727489)
            ·
              refine ⟨6062398976267354842295617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8083198635023139789727489 6062398976267354842295617)
              ·
                refine ⟨4546799232200516131721713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6062398976267354842295617 4546799232200516131721713)
                ·
                  refine ⟨3410099424150387098791285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4546799232200516131721713 3410099424150387098791285)
                  ·
                    refine ⟨319696821014098790511683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3410099424150387098791285 319696821014098790511683)
                    ·
                      rfl

theorem cell23_1867822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_1867822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1867822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1867822 prefixEnd_1867822 := by exact prefixLift 1867822
  have htrace : WordTrace (prefixWord ++ tailWord_1867822) baseStart_1867822 baseEnd_1867822 := by
    simpa [prefixWord, tailWord_1867822, baseEnd_1867822] using wordTrace_append hprefix tailTrace_1867822
  have hstable : (prefixWord ++ tailWord_1867822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867822).length < 2 ^ (prefixWord ++ tailWord_1867822).sum := by decide
  have hdescent : baseEnd_1867822 < baseStart_1867822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867845 : List Nat := [1, 3, 1, 1, 1, 3, 1, 4, 1, 4, 3]
def baseStart_1867845 : Nat := 118140960795 + 1867845 * 2 ^ 59
def prefixEnd_1867845 : Nat := 4983230072969 + 3 ^ 40 * 1867845 * 2
def baseEnd_1867845 : Nat := 959102273097349781547443

theorem tailTrace_1867845 : CollatzResearch.WordTrace tailWord_1867845 prefixEnd_1867845 959102273097349781547443 := by
  unfold tailWord_1867845
  simp only [CollatzResearch.WordTrace]
  refine ⟨68125903918124042374020989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45417269278749361582680659 68125903918124042374020989)
  ·
    refine ⟨25547213969296515890257871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68125903918124042374020989 25547213969296515890257871)
    ·
      refine ⟨38320820953944773835386807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25547213969296515890257871 38320820953944773835386807)
      ·
        refine ⟨57481231430917160753080211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38320820953944773835386807 57481231430917160753080211)
        ·
          refine ⟨86221847146375741129620317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57481231430917160753080211 86221847146375741129620317)
          ·
            refine ⟨32333192679890902923607619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86221847146375741129620317 32333192679890902923607619)
            ·
              refine ⟨48499789019836354385411429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32333192679890902923607619 48499789019836354385411429)
              ·
                refine ⟨9093710441219316447264643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48499789019836354385411429 9093710441219316447264643)
                ·
                  refine ⟨13640565661828974670896965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9093710441219316447264643 13640565661828974670896965)
                  ·
                    refine ⟨2557606061592932750793181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13640565661828974670896965 2557606061592932750793181)
                    ·
                      refine ⟨959102273097349781547443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2557606061592932750793181 959102273097349781547443)
                      ·
                        rfl

theorem cell23_1867845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 4, 3].length) (baseStart_1867845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1867845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1867845 prefixEnd_1867845 := by exact prefixLift 1867845
  have htrace : WordTrace (prefixWord ++ tailWord_1867845) baseStart_1867845 baseEnd_1867845 := by
    simpa [prefixWord, tailWord_1867845, baseEnd_1867845] using wordTrace_append hprefix tailTrace_1867845
  have hstable : (prefixWord ++ tailWord_1867845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867845).length < 2 ^ (prefixWord ++ tailWord_1867845).sum := by decide
  have hdescent : baseEnd_1867845 < baseStart_1867845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867882 : List Nat := [3, 1, 3, 2, 3, 1, 1, 1, 8]
def baseStart_1867882 : Nat := 118140960795 + 1867882 * 2 ^ 59
def prefixEnd_1867882 : Nat := 4983230072969 + 3 ^ 40 * 1867882 * 2
def baseEnd_1867882 : Nat := 106569030209062904087197

theorem tailTrace_1867882 : CollatzResearch.WordTrace tailWord_1867882 prefixEnd_1867882 106569030209062904087197 := by
  unfold tailWord_1867882
  simp only [CollatzResearch.WordTrace]
  refine ⟨17031813354747499423279475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45418168945993331795411933 17031813354747499423279475)
  ·
    refine ⟨25547720032121249134919213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17031813354747499423279475 25547720032121249134919213)
    ·
      refine ⟨9580395012045468425594705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25547720032121249134919213 9580395012045468425594705)
      ·
        refine ⟨7185296259034101319196029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9580395012045468425594705 7185296259034101319196029)
        ·
          refine ⟨2694486097137787994698511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7185296259034101319196029 2694486097137787994698511)
          ·
            refine ⟨4041729145706681992047767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2694486097137787994698511 4041729145706681992047767)
            ·
              refine ⟨6062593718560022988071651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4041729145706681992047767 6062593718560022988071651)
              ·
                refine ⟨9093890577840034482107477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6062593718560022988071651 9093890577840034482107477)
                ·
                  refine ⟨106569030209062904087197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9093890577840034482107477 106569030209062904087197)
                  ·
                    rfl

theorem cell23_1867882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 8].length) (baseStart_1867882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1867882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1867882 prefixEnd_1867882 := by exact prefixLift 1867882
  have htrace : WordTrace (prefixWord ++ tailWord_1867882) baseStart_1867882 baseEnd_1867882 := by
    simpa [prefixWord, tailWord_1867882, baseEnd_1867882] using wordTrace_append hprefix tailTrace_1867882
  have hstable : (prefixWord ++ tailWord_1867882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867882).length < 2 ^ (prefixWord ++ tailWord_1867882).sum := by decide
  have hdescent : baseEnd_1867882 < baseStart_1867882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867885 : List Nat := [1, 5, 1, 1, 2, 1, 1, 1, 1, 1, 8]
def baseStart_1867885 : Nat := 118140960795 + 1867885 * 2 ^ 59
def prefixEnd_1867885 : Nat := 4983230072969 + 3 ^ 40 * 1867885 * 2
def baseEnd_1867885 : Nat := 959122812323529625047259

theorem tailTrace_1867885 : CollatzResearch.WordTrace tailWord_1867885 prefixEnd_1867885 959122812323529625047259 := by
  unfold tailWord_1867885
  simp only [CollatzResearch.WordTrace]
  refine ⟨68127362837979129205477109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45418241891986086136984739 68127362837979129205477109)
  ·
    refine ⟨6386940266060543363013479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68127362837979129205477109 6386940266060543363013479)
    ·
      refine ⟨9580410399090815044520219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6386940266060543363013479 9580410399090815044520219)
      ·
        refine ⟨14370615598636222566780329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9580410399090815044520219 14370615598636222566780329)
        ·
          refine ⟨10777961698977166925085247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14370615598636222566780329 10777961698977166925085247)
          ·
            refine ⟨16166942548465750387627871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10777961698977166925085247 16166942548465750387627871)
            ·
              refine ⟨24250413822698625581441807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16166942548465750387627871 24250413822698625581441807)
              ·
                refine ⟨36375620734047938372162711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24250413822698625581441807 36375620734047938372162711)
                ·
                  refine ⟨54563431101071907558244067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36375620734047938372162711 54563431101071907558244067)
                  ·
                    refine ⟨81845146651607861337366101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54563431101071907558244067 81845146651607861337366101)
                    ·
                      refine ⟨959122812323529625047259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 81845146651607861337366101 959122812323529625047259)
                      ·
                        rfl

theorem cell23_1867885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_1867885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1867885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1867885 prefixEnd_1867885 := by exact prefixLift 1867885
  have htrace : WordTrace (prefixWord ++ tailWord_1867885) baseStart_1867885 baseEnd_1867885 := by
    simpa [prefixWord, tailWord_1867885, baseEnd_1867885] using wordTrace_append hprefix tailTrace_1867885
  have hstable : (prefixWord ++ tailWord_1867885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867885).length < 2 ^ (prefixWord ++ tailWord_1867885).sum := by decide
  have hdescent : baseEnd_1867885 < baseStart_1867885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867909 : List Nat := [1, 3, 1, 1, 5, 1, 2, 2, 3, 1, 3]
def baseStart_1867909 : Nat := 118140960795 + 1867909 * 2 ^ 59
def prefixEnd_1867909 : Nat := 4983230072969 + 3 ^ 40 * 1867909 * 2
def baseEnd_1867909 : Nat := 959135135859237531147149

theorem tailTrace_1867909 : CollatzResearch.WordTrace tailWord_1867909 prefixEnd_1867909 959135135859237531147149 := by
  unfold tailWord_1867909
  simp only [CollatzResearch.WordTrace]
  refine ⟨68128238189892181304350781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45418825459928120869567187 68128238189892181304350781)
  ·
    refine ⟨25548089321209567989131543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68128238189892181304350781 25548089321209567989131543)
    ·
      refine ⟨38322133981814351983697315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25548089321209567989131543 38322133981814351983697315)
      ·
        refine ⟨57483200972721527975545973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38322133981814351983697315 57483200972721527975545973)
        ·
          refine ⟨5389050091192643247707435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57483200972721527975545973 5389050091192643247707435)
          ·
            refine ⟨8083575136788964871561153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5389050091192643247707435 8083575136788964871561153)
            ·
              refine ⟨6062681352591723653670865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8083575136788964871561153 6062681352591723653670865)
              ·
                refine ⟨4547011014443792740253149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6062681352591723653670865 4547011014443792740253149)
                ·
                  refine ⟨1705129130416422277594931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4547011014443792740253149 1705129130416422277594931)
                  ·
                    refine ⟨2557693695624633416392397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1705129130416422277594931 2557693695624633416392397)
                    ·
                      refine ⟨959135135859237531147149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2557693695624633416392397 959135135859237531147149)
                      ·
                        rfl

theorem cell23_1867909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 2, 3, 1, 3].length) (baseStart_1867909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1867909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1867909 prefixEnd_1867909 := by exact prefixLift 1867909
  have htrace : WordTrace (prefixWord ++ tailWord_1867909) baseStart_1867909 baseEnd_1867909 := by
    simpa [prefixWord, tailWord_1867909, baseEnd_1867909] using wordTrace_append hprefix tailTrace_1867909
  have hstable : (prefixWord ++ tailWord_1867909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867909).length < 2 ^ (prefixWord ++ tailWord_1867909).sum := by decide
  have hdescent : baseEnd_1867909 < baseStart_1867909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867925 : List Nat := [1, 3, 2, 1, 1, 1, 4, 1, 3, 6]
def baseStart_1867925 : Nat := 118140960795 + 1867925 * 2 ^ 59
def prefixEnd_1867925 : Nat := 4983230072969 + 3 ^ 40 * 1867925 * 2
def baseEnd_1867925 : Nat := 319714450516569822849025

theorem tailTrace_1867925 : CollatzResearch.WordTrace tailWord_1867925 prefixEnd_1867925 319714450516569822849025 := by
  unfold tailWord_1867925
  simp only [CollatzResearch.WordTrace]
  refine ⟨68128821757834216036933229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45419214505222810691288819 68128821757834216036933229)
  ·
    refine ⟨25548308159187831013849961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68128821757834216036933229 25548308159187831013849961)
    ·
      refine ⟨19161231119390873260387471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25548308159187831013849961 19161231119390873260387471)
      ·
        refine ⟨28741846679086309890581207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19161231119390873260387471 28741846679086309890581207)
        ·
          refine ⟨43112770018629464835871811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28741846679086309890581207 43112770018629464835871811)
          ·
            refine ⟨64669155027944197253807717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43112770018629464835871811 64669155027944197253807717)
            ·
              refine ⟨12125466567739536985088947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64669155027944197253807717 12125466567739536985088947)
              ·
                refine ⟨18188199851609305477633421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12125466567739536985088947 18188199851609305477633421)
                ·
                  refine ⟨6820574944353489554112533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18188199851609305477633421 6820574944353489554112533)
                  ·
                    refine ⟨319714450516569822849025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6820574944353489554112533 319714450516569822849025)
                    ·
                      rfl

theorem cell23_1867925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 3, 6].length) (baseStart_1867925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1867925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1867925 prefixEnd_1867925 := by exact prefixLift 1867925
  have htrace : WordTrace (prefixWord ++ tailWord_1867925) baseStart_1867925 baseEnd_1867925 := by
    simpa [prefixWord, tailWord_1867925, baseEnd_1867925] using wordTrace_append hprefix tailTrace_1867925
  have hstable : (prefixWord ++ tailWord_1867925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867925).length < 2 ^ (prefixWord ++ tailWord_1867925).sum := by decide
  have hdescent : baseEnd_1867925 < baseStart_1867925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867943 : List Nat := [1, 1, 6, 2, 2, 2, 1, 1, 3, 1, 3]
def baseStart_1867943 : Nat := 118140960795 + 1867943 * 2 ^ 59
def prefixEnd_1867943 : Nat := 4983230072969 + 3 ^ 40 * 1867943 * 2
def baseEnd_1867943 : Nat := 959152594201490398121993

theorem tailTrace_1867943 : CollatzResearch.WordTrace tailWord_1867943 prefixEnd_1867943 959152594201490398121993 := by
  unfold tailWord_1867943
  simp only [CollatzResearch.WordTrace]
  refine ⟨68129478271769005111088483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45419652181179336740725655 68129478271769005111088483)
  ·
    refine ⟨102194217407653507666632725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68129478271769005111088483 102194217407653507666632725)
    ·
      refine ⟨4790353940983758171873409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 102194217407653507666632725 4790353940983758171873409)
      ·
        refine ⟨3592765455737818628905057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4790353940983758171873409 3592765455737818628905057)
        ·
          refine ⟨2694574091803363971678793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3592765455737818628905057 2694574091803363971678793)
          ·
            refine ⟨2020930568852522978759095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2694574091803363971678793 2020930568852522978759095)
            ·
              refine ⟨3031395853278784468138643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2020930568852522978759095 3031395853278784468138643)
              ·
                refine ⟨4547093779918176702207965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3031395853278784468138643 4547093779918176702207965)
                ·
                  refine ⟨1705160167469316263327987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4547093779918176702207965 1705160167469316263327987)
                  ·
                    refine ⟨2557740251203974394991981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1705160167469316263327987 2557740251203974394991981)
                    ·
                      refine ⟨959152594201490398121993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2557740251203974394991981 959152594201490398121993)
                      ·
                        rfl

theorem cell23_1867943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_1867943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1867943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1867943 prefixEnd_1867943 := by exact prefixLift 1867943
  have htrace : WordTrace (prefixWord ++ tailWord_1867943) baseStart_1867943 baseEnd_1867943 := by
    simpa [prefixWord, tailWord_1867943, baseEnd_1867943] using wordTrace_append hprefix tailTrace_1867943
  have hstable : (prefixWord ++ tailWord_1867943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867943).length < 2 ^ (prefixWord ++ tailWord_1867943).sum := by decide
  have hdescent : baseEnd_1867943 < baseStart_1867943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867950 : List Nat := [4, 1, 4, 2, 2, 1, 2, 1, 6]
def baseStart_1867950 : Nat := 118140960795 + 1867950 * 2 ^ 59
def prefixEnd_1867950 : Nat := 4983230072969 + 3 ^ 40 * 1867950 * 2
def baseEnd_1867950 : Nat := 106572909840674652303829

theorem tailTrace_1867950 : CollatzResearch.WordTrace tailWord_1867950 prefixEnd_1867950 106572909840674652303829 := by
  unfold tailWord_1867950
  simp only [CollatzResearch.WordTrace]
  refine ⟨8516216697842955663324163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45419822388495763537728869 8516216697842955663324163)
  ·
    refine ⟨12774325046764433494986245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8516216697842955663324163 12774325046764433494986245)
    ·
      refine ⟨2395185946268331280309921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12774325046764433494986245 2395185946268331280309921)
      ·
        refine ⟨1796389459701248460232441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2395185946268331280309921 1796389459701248460232441)
        ·
          refine ⟨1347292094775936345174331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1796389459701248460232441 1347292094775936345174331)
          ·
            refine ⟨2020938142163904517761497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1347292094775936345174331 2020938142163904517761497)
            ·
              refine ⟨1515703606622928388321123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2020938142163904517761497 1515703606622928388321123)
              ·
                refine ⟨2273555409934392582481685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1515703606622928388321123 2273555409934392582481685)
                ·
                  refine ⟨106572909840674652303829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2273555409934392582481685 106572909840674652303829)
                  ·
                    rfl

theorem cell23_1867950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 2, 1, 6].length) (baseStart_1867950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1867950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1867950 prefixEnd_1867950 := by exact prefixLift 1867950
  have htrace : WordTrace (prefixWord ++ tailWord_1867950) baseStart_1867950 baseEnd_1867950 := by
    simpa [prefixWord, tailWord_1867950, baseEnd_1867950] using wordTrace_append hprefix tailTrace_1867950
  have hstable : (prefixWord ++ tailWord_1867950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867950).length < 2 ^ (prefixWord ++ tailWord_1867950).sum := by decide
  have hdescent : baseEnd_1867950 < baseStart_1867950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867959 : List Nat := [1, 1, 3, 1, 4, 3, 1, 3, 2, 4]
def baseStart_1867959 : Nat := 118140960795 + 1867959 * 2 ^ 59
def prefixEnd_1867959 : Nat := 4983230072969 + 3 ^ 40 * 1867959 * 2
def baseEnd_1867959 : Nat := 319720269963987445173973

theorem tailTrace_1867959 : CollatzResearch.WordTrace tailWord_1867959 prefixEnd_1867959 319720269963987445173973 := by
  unfold tailWord_1867959
  simp only [CollatzResearch.WordTrace]
  refine ⟨68130061839711039843670931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45420041226474026562447287 68130061839711039843670931)
  ·
    refine ⟨102195092759566559765506397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68130061839711039843670931 102195092759566559765506397)
    ·
      refine ⟨38323159784837459912064899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102195092759566559765506397 38323159784837459912064899)
      ·
        refine ⟨57484739677256189868097349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38323159784837459912064899 57484739677256189868097349)
        ·
          refine ⟨10778388689485535600268253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57484739677256189868097349 10778388689485535600268253)
          ·
            refine ⟨4041895758557075850100595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10778388689485535600268253 4041895758557075850100595)
            ·
              refine ⟨6062843637835613775150893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4041895758557075850100595 6062843637835613775150893)
              ·
                refine ⟨2273566364188355165681585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6062843637835613775150893 2273566364188355165681585)
                ·
                  refine ⟨1705174773141266374261189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2273566364188355165681585 1705174773141266374261189)
                  ·
                    refine ⟨319720269963987445173973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1705174773141266374261189 319720269963987445173973)
                    ·
                      rfl

theorem cell23_1867959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 3, 2, 4].length) (baseStart_1867959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1867959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1867959 prefixEnd_1867959 := by exact prefixLift 1867959
  have htrace : WordTrace (prefixWord ++ tailWord_1867959) baseStart_1867959 baseEnd_1867959 := by
    simpa [prefixWord, tailWord_1867959, baseEnd_1867959] using wordTrace_append hprefix tailTrace_1867959
  have hstable : (prefixWord ++ tailWord_1867959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867959).length < 2 ^ (prefixWord ++ tailWord_1867959).sum := by decide
  have hdescent : baseEnd_1867959 < baseStart_1867959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867970 : List Nat := [3, 5, 1, 1, 1, 2, 2, 1, 2, 3, 2]
def baseStart_1867970 : Nat := 118140960795 + 1867970 * 2 ^ 59
def prefixEnd_1867970 : Nat := 4983230072969 + 3 ^ 40 * 1867970 * 2
def baseEnd_1867970 : Nat := 959166458179161792484369

theorem tailTrace_1867970 : CollatzResearch.WordTrace tailWord_1867970 prefixEnd_1867970 959166458179161792484369 := by
  unfold tailWord_1867970
  simp only [CollatzResearch.WordTrace]
  refine ⟨17032615760667797180580341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45420308695114125814880909 17032615760667797180580341)
  ·
    refine ⟨1596807727562605985679407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17032615760667797180580341 1596807727562605985679407)
    ·
      refine ⟨2395211591343908978519111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1596807727562605985679407 2395211591343908978519111)
      ·
        refine ⟨3592817387015863467778667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2395211591343908978519111 3592817387015863467778667)
        ·
          refine ⟨5389226080523795201668001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3592817387015863467778667 5389226080523795201668001)
          ·
            refine ⟨4041919560392846401251001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5389226080523795201668001 4041919560392846401251001)
            ·
              refine ⟨3031439670294634800938251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4041919560392846401251001 3031439670294634800938251)
              ·
                refine ⟨4547159505441952201407377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3031439670294634800938251 4547159505441952201407377)
                ·
                  refine ⟨3410369629081464151055533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4547159505441952201407377 3410369629081464151055533)
                  ·
                    refine ⟨1278888610905549056645825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3410369629081464151055533 1278888610905549056645825)
                    ·
                      refine ⟨959166458179161792484369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1278888610905549056645825 959166458179161792484369)
                      ·
                        rfl

theorem cell23_1867970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_1867970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1867970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1867970 prefixEnd_1867970 := by exact prefixLift 1867970
  have htrace : WordTrace (prefixWord ++ tailWord_1867970) baseStart_1867970 baseEnd_1867970 := by
    simpa [prefixWord, tailWord_1867970, baseEnd_1867970] using wordTrace_append hprefix tailTrace_1867970
  have hstable : (prefixWord ++ tailWord_1867970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867970).length < 2 ^ (prefixWord ++ tailWord_1867970).sum := by decide
  have hdescent : baseEnd_1867970 < baseStart_1867970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867972 : List Nat := [2, 3, 3, 1, 2, 1, 2, 9]
def baseStart_1867972 : Nat := 118140960795 + 1867972 * 2 ^ 59
def prefixEnd_1867972 : Nat := 4983230072969 + 3 ^ 40 * 1867972 * 2
def baseEnd_1867972 : Nat := 35524721671869288320717

theorem tailTrace_1867972 : CollatzResearch.WordTrace tailWord_1867972 prefixEnd_1867972 35524721671869288320717 := by
  unfold tailWord_1867972
  simp only [CollatzResearch.WordTrace]
  refine ⟨34065267994331971531947085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45420357325775962042596113 34065267994331971531947085)
  ·
    refine ⟨12774475497874489324480157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34065267994331971531947085 12774475497874489324480157)
    ·
      refine ⟨4790428311702933496680059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12774475497874489324480157 4790428311702933496680059)
      ·
        refine ⟨7185642467554400245020089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4790428311702933496680059 7185642467554400245020089)
        ·
          refine ⟨5389231850665800183765067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7185642467554400245020089 5389231850665800183765067)
          ·
            refine ⟨8083847775998700275647601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5389231850665800183765067 8083847775998700275647601)
            ·
              refine ⟨6062885831999025206735701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8083847775998700275647601 6062885831999025206735701)
              ·
                refine ⟨35524721671869288320717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6062885831999025206735701 35524721671869288320717)
                ·
                  rfl

theorem cell23_1867972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 9].length) (baseStart_1867972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1867972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1867972 prefixEnd_1867972 := by exact prefixLift 1867972
  have htrace : WordTrace (prefixWord ++ tailWord_1867972) baseStart_1867972 baseEnd_1867972 := by
    simpa [prefixWord, tailWord_1867972, baseEnd_1867972] using wordTrace_append hprefix tailTrace_1867972
  have hstable : (prefixWord ++ tailWord_1867972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867972).length < 2 ^ (prefixWord ++ tailWord_1867972).sum := by decide
  have hdescent : baseEnd_1867972 < baseStart_1867972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867995 : List Nat := [1, 1, 1, 1, 1, 1, 1, 5, 4, 2, 5]
def baseStart_1867995 : Nat := 118140960795 + 1867995 * 2 ^ 59
def prefixEnd_1867995 : Nat := 4983230072969 + 3 ^ 40 * 1867995 * 2
def baseEnd_1867995 : Nat := 959179295195524194671753

theorem tailTrace_1867995 : CollatzResearch.WordTrace tailWord_1867995 prefixEnd_1867995 959179295195524194671753 := by
  unfold tailWord_1867995
  simp only [CollatzResearch.WordTrace]
  refine ⟨68131374867580617991981439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45420916578387078661320959 68131374867580617991981439)
  ·
    refine ⟨102197062301370926987972159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68131374867580617991981439 102197062301370926987972159)
    ·
      refine ⟨153295593452056390481958239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102197062301370926987972159 153295593452056390481958239)
      ·
        refine ⟨229943390178084585722937359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153295593452056390481958239 229943390178084585722937359)
        ·
          refine ⟨344915085267126878584406039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229943390178084585722937359 344915085267126878584406039)
          ·
            refine ⟨517372627900690317876609059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344915085267126878584406039 517372627900690317876609059)
            ·
              refine ⟨776058941851035476814913589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 517372627900690317876609059 776058941851035476814913589)
              ·
                refine ⟨72755525798534575951398149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 776058941851035476814913589 72755525798534575951398149)
                ·
                  refine ⟨13641661087225232990887153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72755525798534575951398149 13641661087225232990887153)
                  ·
                    refine ⟨10231245815418924743165365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13641661087225232990887153 10231245815418924743165365)
                    ·
                      refine ⟨959179295195524194671753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10231245815418924743165365 959179295195524194671753)
                      ·
                        rfl

theorem cell23_1867995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 2, 5].length) (baseStart_1867995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1867995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1867995 prefixEnd_1867995 := by exact prefixLift 1867995
  have htrace : WordTrace (prefixWord ++ tailWord_1867995) baseStart_1867995 baseEnd_1867995 := by
    simpa [prefixWord, tailWord_1867995, baseEnd_1867995] using wordTrace_append hprefix tailTrace_1867995
  have hstable : (prefixWord ++ tailWord_1867995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867995).length < 2 ^ (prefixWord ++ tailWord_1867995).sum := by decide
  have hdescent : baseEnd_1867995 < baseStart_1867995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868042 : List Nat := [3, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5]
def baseStart_1868042 : Nat := 118140960795 + 1868042 * 2 ^ 59
def prefixEnd_1868042 : Nat := 4983230072969 + 3 ^ 40 * 1868042 * 2
def baseEnd_1868042 : Nat := 959203428786285510784037

theorem tailTrace_1868042 : CollatzResearch.WordTrace tailWord_1868042 prefixEnd_1868042 959203428786285510784037 := by
  unfold tailWord_1868042
  simp only [CollatzResearch.WordTrace]
  refine ⟨17033272274602586254735595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45422059398940230012628253 17033272274602586254735595)
  ·
    refine ⟨25549908411903879382103393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17033272274602586254735595 25549908411903879382103393)
    ·
      refine ⟨19162431308927909536577545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25549908411903879382103393 19162431308927909536577545)
      ·
        refine ⟨14371823481695932152433159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19162431308927909536577545 14371823481695932152433159)
        ·
          refine ⟨21557735222543898228649739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14371823481695932152433159 21557735222543898228649739)
          ·
            refine ⟨32336602833815847342974609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21557735222543898228649739 32336602833815847342974609)
            ·
              refine ⟨24252452125361885507230957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32336602833815847342974609 24252452125361885507230957)
              ·
                refine ⟨9094669547010707065211609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24252452125361885507230957 9094669547010707065211609)
                ·
                  refine ⟨6821002160258030298908707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9094669547010707065211609 6821002160258030298908707)
                  ·
                    refine ⟨10231503240387045448363061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6821002160258030298908707 10231503240387045448363061)
                    ·
                      refine ⟨959203428786285510784037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10231503240387045448363061 959203428786285510784037)
                      ·
                        rfl

theorem cell23_1868042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_1868042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1868042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1868042 prefixEnd_1868042 := by exact prefixLift 1868042
  have htrace : WordTrace (prefixWord ++ tailWord_1868042) baseStart_1868042 baseEnd_1868042 := by
    simpa [prefixWord, tailWord_1868042, baseEnd_1868042] using wordTrace_append hprefix tailTrace_1868042
  have hstable : (prefixWord ++ tailWord_1868042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868042).length < 2 ^ (prefixWord ++ tailWord_1868042).sum := by decide
  have hdescent : baseEnd_1868042 < baseStart_1868042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868056 : List Nat := [2, 1, 2, 3, 1, 2, 3, 1, 4, 2, 2]
def baseStart_1868056 : Nat := 118140960795 + 1868056 * 2 ^ 59
def prefixEnd_1868056 : Nat := 4983230072969 + 3 ^ 40 * 1868056 * 2
def baseEnd_1868056 : Nat := 959210617515448456008973

theorem tailTrace_1868056 : CollatzResearch.WordTrace tailWord_1868056 prefixEnd_1868056 959210617515448456008973 := by
  unfold tailWord_1868056
  simp only [CollatzResearch.WordTrace]
  refine ⟨34066799860179812704976011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45422399813573083606634681 34066799860179812704976011)
  ·
    refine ⟨51100199790269719057464017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34066799860179812704976011 51100199790269719057464017)
    ·
      refine ⟨38325149842702289293098013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51100199790269719057464017 38325149842702289293098013)
      ·
        refine ⟨14371931191013358484911755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38325149842702289293098013 14371931191013358484911755)
        ·
          refine ⟨21557896786520037727367633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14371931191013358484911755 21557896786520037727367633)
          ·
            refine ⟨16168422589890028295525725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21557896786520037727367633 16168422589890028295525725)
            ·
              refine ⟨6063158471208760610822147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16168422589890028295525725 6063158471208760610822147)
              ·
                refine ⟨9094737706813140916233221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6063158471208760610822147 9094737706813140916233221)
                ·
                  refine ⟨1705263320027463921793729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9094737706813140916233221 1705263320027463921793729)
                  ·
                    refine ⟨1278947490020597941345297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1705263320027463921793729 1278947490020597941345297)
                    ·
                      refine ⟨959210617515448456008973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1278947490020597941345297 959210617515448456008973)
                      ·
                        rfl

theorem cell23_1868056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 4, 2, 2].length) (baseStart_1868056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1868056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1868056 prefixEnd_1868056 := by exact prefixLift 1868056
  have htrace : WordTrace (prefixWord ++ tailWord_1868056) baseStart_1868056 baseEnd_1868056 := by
    simpa [prefixWord, tailWord_1868056, baseEnd_1868056] using wordTrace_append hprefix tailTrace_1868056
  have hstable : (prefixWord ++ tailWord_1868056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868056).length < 2 ^ (prefixWord ++ tailWord_1868056).sum := by decide
  have hdescent : baseEnd_1868056 < baseStart_1868056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868092 : List Nat := [2, 2, 2, 2, 1, 2, 1, 3, 1, 7]
def baseStart_1868092 : Nat := 118140960795 + 1868092 * 2 ^ 59
def prefixEnd_1868092 : Nat := 4983230072969 + 3 ^ 40 * 1868092 * 2
def baseEnd_1868092 : Nat := 319743034273003438386269

theorem tailTrace_1868092 : CollatzResearch.WordTrace tailWord_1868092 prefixEnd_1868092 319743034273003438386269 := by
  unfold tailWord_1868092
  simp only [CollatzResearch.WordTrace]
  refine ⟨34067456374114601779131265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45423275165486135705508353 34067456374114601779131265)
  ·
    refine ⟨25550592280585951334348449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34067456374114601779131265 25550592280585951334348449)
    ·
      refine ⟨19162944210439463500761337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25550592280585951334348449 19162944210439463500761337)
      ·
        refine ⟨14372208157829597625571003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19162944210439463500761337 14372208157829597625571003)
        ·
          refine ⟨21558312236744396438356505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14372208157829597625571003 21558312236744396438356505)
          ·
            refine ⟨16168734177558297328767379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21558312236744396438356505 16168734177558297328767379)
            ·
              refine ⟨24253101266337445993151069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16168734177558297328767379 24253101266337445993151069)
              ·
                refine ⟨9094912974876542247431651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24253101266337445993151069 9094912974876542247431651)
                ·
                  refine ⟨13642369462314813371147477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9094912974876542247431651 13642369462314813371147477)
                  ·
                    refine ⟨319743034273003438386269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13642369462314813371147477 319743034273003438386269)
                    ·
                      rfl

theorem cell23_1868092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 1, 7].length) (baseStart_1868092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1868092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1868092 prefixEnd_1868092 := by exact prefixLift 1868092
  have htrace : WordTrace (prefixWord ++ tailWord_1868092) baseStart_1868092 baseEnd_1868092 := by
    simpa [prefixWord, tailWord_1868092, baseEnd_1868092] using wordTrace_append hprefix tailTrace_1868092
  have hstable : (prefixWord ++ tailWord_1868092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868092).length < 2 ^ (prefixWord ++ tailWord_1868092).sum := by decide
  have hdescent : baseEnd_1868092 < baseStart_1868092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868124 : List Nat := [2, 2, 4, 3, 1, 2, 2, 1, 2, 2, 2]
def baseStart_1868124 : Nat := 118140960795 + 1868124 * 2 ^ 59
def prefixEnd_1868124 : Nat := 4983230072969 + 3 ^ 40 * 1868124 * 2
def baseEnd_1868124 : Nat := 959245534199954189958661

theorem tailTrace_1868124 : CollatzResearch.WordTrace tailWord_1868124 prefixEnd_1868124 959245534199954189958661 := by
  unfold tailWord_1868124
  simp only [CollatzResearch.WordTrace]
  refine ⟨34068039942056636511713713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45424053256075515348951617 34068039942056636511713713)
  ·
    refine ⟨25551029956542477383785285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34068039942056636511713713 25551029956542477383785285)
    ·
      refine ⟨4790818116851714509459741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25551029956542477383785285 4790818116851714509459741)
      ·
        refine ⟨1796556793819392941047403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4790818116851714509459741 1796556793819392941047403)
        ·
          refine ⟨2694835190729089411571105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1796556793819392941047403 2694835190729089411571105)
          ·
            refine ⟨2021126393046817058678329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2694835190729089411571105 2021126393046817058678329)
            ·
              refine ⟨1515844794785112794008747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2021126393046817058678329 1515844794785112794008747)
              ·
                refine ⟨2273767192177669191013121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1515844794785112794008747 2273767192177669191013121)
                ·
                  refine ⟨1705325394133251893259841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2273767192177669191013121 1705325394133251893259841)
                  ·
                    refine ⟨1278994045599938919944881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1705325394133251893259841 1278994045599938919944881)
                    ·
                      refine ⟨959245534199954189958661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1278994045599938919944881 959245534199954189958661)
                      ·
                        rfl

theorem cell23_1868124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_1868124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1868124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1868124 prefixEnd_1868124 := by exact prefixLift 1868124
  have htrace : WordTrace (prefixWord ++ tailWord_1868124) baseStart_1868124 baseEnd_1868124 := by
    simpa [prefixWord, tailWord_1868124, baseEnd_1868124] using wordTrace_append hprefix tailTrace_1868124
  have hstable : (prefixWord ++ tailWord_1868124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868124).length < 2 ^ (prefixWord ++ tailWord_1868124).sum := by decide
  have hdescent : baseEnd_1868124 < baseStart_1868124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868146 : List Nat := [3, 2, 1, 2, 1, 4, 2, 1, 2, 1, 4]
def baseStart_1868146 : Nat := 118140960795 + 1868146 * 2 ^ 59
def prefixEnd_1868146 : Nat := 4983230072969 + 3 ^ 40 * 1868146 * 2
def baseEnd_1868146 : Nat := 959256830774353103883559

theorem tailTrace_1868146 : CollatzResearch.WordTrace tailWord_1868146 prefixEnd_1868146 959256830774353103883559 := by
  unfold tailWord_1868146
  simp only [CollatzResearch.WordTrace]
  refine ⟨17034220572508392695182073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45424588193355713853818861 17034220572508392695182073)
  ·
    refine ⟨12775665429381294521386555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17034220572508392695182073 12775665429381294521386555)
    ·
      refine ⟨19163498144071941782079833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12775665429381294521386555 19163498144071941782079833)
      ·
        refine ⟨14372623608053956336559875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19163498144071941782079833 14372623608053956336559875)
        ·
          refine ⟨21558935412080934504839813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14372623608053956336559875 21558935412080934504839813)
          ·
            refine ⟨4042300389765175219657465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21558935412080934504839813 4042300389765175219657465)
            ·
              refine ⟨3031725292323881414743099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4042300389765175219657465 3031725292323881414743099)
              ·
                refine ⟨4547587938485822122114649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3031725292323881414743099 4547587938485822122114649)
                ·
                  refine ⟨3410690953864366591585987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4547587938485822122114649 3410690953864366591585987)
                  ·
                    refine ⟨5116036430796549887378981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3410690953864366591585987 5116036430796549887378981)
                    ·
                      refine ⟨959256830774353103883559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5116036430796549887378981 959256830774353103883559)
                      ·
                        rfl

theorem cell23_1868146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_1868146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1868146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1868146 prefixEnd_1868146 := by exact prefixLift 1868146
  have htrace : WordTrace (prefixWord ++ tailWord_1868146) baseStart_1868146 baseEnd_1868146 := by
    simpa [prefixWord, tailWord_1868146, baseEnd_1868146] using wordTrace_append hprefix tailTrace_1868146
  have hstable : (prefixWord ++ tailWord_1868146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868146).length < 2 ^ (prefixWord ++ tailWord_1868146).sum := by decide
  have hdescent : baseEnd_1868146 < baseStart_1868146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868169 : List Nat := [1, 2, 1, 1, 6, 1, 1, 4, 6]
def baseStart_1868169 : Nat := 118140960795 + 1868169 * 2 ^ 59
def prefixEnd_1868169 : Nat := 4983230072969 + 3 ^ 40 * 1868169 * 2
def baseEnd_1868169 : Nat := 106585404536600723766217

theorem tailTrace_1868169 : CollatzResearch.WordTrace tailWord_1868169 prefixEnd_1868169 106585404536600723766217 := by
  unfold tailWord_1868169
  simp only [CollatzResearch.WordTrace]
  refine ⟨68137721168950245708815561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45425147445966830472543707 68137721168950245708815561)
  ·
    refine ⟨51103290876712684281611671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68137721168950245708815561 51103290876712684281611671)
    ·
      refine ⟨76654936315069026422417507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51103290876712684281611671 76654936315069026422417507)
      ·
        refine ⟨114982404472603539633626261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76654936315069026422417507 114982404472603539633626261)
        ·
          refine ⟨5389800209653290920326231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 114982404472603539633626261 5389800209653290920326231)
          ·
            refine ⟨8084700314479936380489347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5389800209653290920326231 8084700314479936380489347)
            ·
              refine ⟨12127050471719904570734021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8084700314479936380489347 12127050471719904570734021)
              ·
                refine ⟨2273821963447482107012629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12127050471719904570734021 2273821963447482107012629)
                ·
                  refine ⟨106585404536600723766217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2273821963447482107012629 106585404536600723766217)
                  ·
                    rfl

theorem cell23_1868169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 4, 6].length) (baseStart_1868169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1868169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1868169 prefixEnd_1868169 := by exact prefixLift 1868169
  have htrace : WordTrace (prefixWord ++ tailWord_1868169) baseStart_1868169 baseEnd_1868169 := by
    simpa [prefixWord, tailWord_1868169, baseEnd_1868169] using wordTrace_append hprefix tailTrace_1868169
  have hstable : (prefixWord ++ tailWord_1868169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868169).length < 2 ^ (prefixWord ++ tailWord_1868169).sum := by decide
  have hdescent : baseEnd_1868169 < baseStart_1868169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868196 : List Nat := [2, 3, 1, 2, 1, 1, 3, 1, 5, 1, 3]
def baseStart_1868196 : Nat := 118140960795 + 1868196 * 2 ^ 59
def prefixEnd_1868196 : Nat := 4983230072969 + 3 ^ 40 * 1868196 * 2
def baseEnd_1868196 : Nat := 959282504807077908258329

theorem tailTrace_1868196 : CollatzResearch.WordTrace tailWord_1868196 prefixEnd_1868196 959282504807077908258329 := by
  unfold tailWord_1868196
  simp only [CollatzResearch.WordTrace]
  refine ⟨34069352969926214660024221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45425803959901619546698961 34069352969926214660024221)
  ·
    refine ⟨12776007363722330497509083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34069352969926214660024221 12776007363722330497509083)
    ·
      refine ⟨19164011045583495746263625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12776007363722330497509083 19164011045583495746263625)
      ·
        refine ⟨14373008284187621809697719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19164011045583495746263625 14373008284187621809697719)
        ·
          refine ⟨21559512426281432714546579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14373008284187621809697719 21559512426281432714546579)
          ·
            refine ⟨32339268639422149071819869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21559512426281432714546579 32339268639422149071819869)
            ·
              refine ⟨12127225739783305901932451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32339268639422149071819869 12127225739783305901932451)
              ·
                refine ⟨18190838609674958852898677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12127225739783305901932451 18190838609674958852898677)
                ·
                  refine ⟨1705391119657027392459251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18190838609674958852898677 1705391119657027392459251)
                  ·
                    refine ⟨2558086679485541088688877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1705391119657027392459251 2558086679485541088688877)
                    ·
                      refine ⟨959282504807077908258329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2558086679485541088688877 959282504807077908258329)
                      ·
                        rfl

theorem cell23_1868196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 5, 1, 3].length) (baseStart_1868196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1868196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1868196 prefixEnd_1868196 := by exact prefixLift 1868196
  have htrace : WordTrace (prefixWord ++ tailWord_1868196) baseStart_1868196 baseEnd_1868196 := by
    simpa [prefixWord, tailWord_1868196, baseEnd_1868196] using wordTrace_append hprefix tailTrace_1868196
  have hstable : (prefixWord ++ tailWord_1868196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868196).length < 2 ^ (prefixWord ++ tailWord_1868196).sum := by decide
  have hdescent : baseEnd_1868196 < baseStart_1868196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868200 : List Nat := [2, 1, 6, 1, 1, 3, 1, 1, 2, 2, 3]
def baseStart_1868200 : Nat := 118140960795 + 1868200 * 2 ^ 59
def prefixEnd_1868200 : Nat := 4983230072969 + 3 ^ 40 * 1868200 * 2
def baseEnd_1868200 : Nat := 959284558729695892608311

theorem tailTrace_1868200 : CollatzResearch.WordTrace tailWord_1868200 prefixEnd_1868200 959284558729695892608311 := by
  unfold tailWord_1868200
  simp only [CollatzResearch.WordTrace]
  refine ⟨34069425915918969001597027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45425901221225292002129369 34069425915918969001597027)
  ·
    refine ⟨51104138873878453502395541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34069425915918969001597027 51104138873878453502395541)
    ·
      refine ⟨2395506509713052507924791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 51104138873878453502395541 2395506509713052507924791)
      ·
        refine ⟨3593259764569578761887187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2395506509713052507924791 3593259764569578761887187)
        ·
          refine ⟨5389889646854368142830781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3593259764569578761887187 5389889646854368142830781)
          ·
            refine ⟨2021208617570388053561543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5389889646854368142830781 2021208617570388053561543)
            ·
              refine ⟨3031812926355582080342315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2021208617570388053561543 3031812926355582080342315)
              ·
                refine ⟨4547719389533373120513473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3031812926355582080342315 4547719389533373120513473)
                ·
                  refine ⟨3410789542150029840385105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4547719389533373120513473 3410789542150029840385105)
                  ·
                    refine ⟨2558092156612522380288829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3410789542150029840385105 2558092156612522380288829)
                    ·
                      refine ⟨959284558729695892608311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2558092156612522380288829 959284558729695892608311)
                      ·
                        rfl

theorem cell23_1868200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_1868200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1868200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1868200 prefixEnd_1868200 := by exact prefixLift 1868200
  have htrace : WordTrace (prefixWord ++ tailWord_1868200) baseStart_1868200 baseEnd_1868200 := by
    simpa [prefixWord, tailWord_1868200, baseEnd_1868200] using wordTrace_append hprefix tailTrace_1868200
  have hstable : (prefixWord ++ tailWord_1868200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868200).length < 2 ^ (prefixWord ++ tailWord_1868200).sum := by decide
  have hdescent : baseEnd_1868200 < baseStart_1868200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868249 : List Nat := [1, 2, 1, 2, 4, 1, 3, 1, 1, 1, 6]
def baseStart_1868249 : Nat := 118140960795 + 1868249 * 2 ^ 59
def prefixEnd_1868249 : Nat := 4983230072969 + 3 ^ 40 * 1868249 * 2
def baseEnd_1868249 : Nat := 959309719281766200895585

theorem tailTrace_1868249 : CollatzResearch.WordTrace tailWord_1868249 prefixEnd_1868249 959309719281766200895585 := by
  unfold tailWord_1868249
  simp only [CollatzResearch.WordTrace]
  refine ⟨68140639008660419371727801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45427092672440279581151867 68140639008660419371727801)
  ·
    refine ⟨51105479256495314528795851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68140639008660419371727801 51105479256495314528795851)
    ·
      refine ⟨76658218884742971793193777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51105479256495314528795851 76658218884742971793193777)
      ·
        refine ⟨57493664163557228844895333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76658218884742971793193777 57493664163557228844895333)
        ·
          refine ⟨10780062030666980408417875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57493664163557228844895333 10780062030666980408417875)
          ·
            refine ⟨16170093046000470612626813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10780062030666980408417875 16170093046000470612626813)
            ·
              refine ⟨6063784892250176479735055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16170093046000470612626813 6063784892250176479735055)
              ·
                refine ⟨9095677338375264719602583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6063784892250176479735055 9095677338375264719602583)
                ·
                  refine ⟨13643516007562897079403875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9095677338375264719602583 13643516007562897079403875)
                  ·
                    refine ⟨20465274011344345619105813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13643516007562897079403875 20465274011344345619105813)
                    ·
                      refine ⟨959309719281766200895585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20465274011344345619105813 959309719281766200895585)
                      ·
                        rfl

theorem cell23_1868249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 1, 6].length) (baseStart_1868249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1868249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1868249 prefixEnd_1868249 := by exact prefixLift 1868249
  have htrace : WordTrace (prefixWord ++ tailWord_1868249) baseStart_1868249 baseEnd_1868249 := by
    simpa [prefixWord, tailWord_1868249, baseEnd_1868249] using wordTrace_append hprefix tailTrace_1868249
  have hstable : (prefixWord ++ tailWord_1868249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868249).length < 2 ^ (prefixWord ++ tailWord_1868249).sum := by decide
  have hdescent : baseEnd_1868249 < baseStart_1868249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868253 : List Nat := [1, 4, 3, 1, 1, 1, 4, 2, 1, 1, 4]
def baseStart_1868253 : Nat := 118140960795 + 1868253 * 2 ^ 59
def prefixEnd_1868253 : Nat := 4983230072969 + 3 ^ 40 * 1868253 * 2
def baseEnd_1868253 : Nat := 959311773204384185245567

theorem tailTrace_1868253 : CollatzResearch.WordTrace tailWord_1868253 prefixEnd_1868253 959311773204384185245567 := by
  unfold tailWord_1868253
  simp only [CollatzResearch.WordTrace]
  refine ⟨68140784900645928054873413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45427189933763952036582275 68140784900645928054873413)
  ·
    refine ⟨12776397168871111510288765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68140784900645928054873413 12776397168871111510288765)
    ·
      refine ⟨4791148938326666816358287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12776397168871111510288765 4791148938326666816358287)
      ·
        refine ⟨7186723407490000224537431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4791148938326666816358287 7186723407490000224537431)
        ·
          refine ⟨10780085111235000336806147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7186723407490000224537431 10780085111235000336806147)
          ·
            refine ⟨16170127666852500505209221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10780085111235000336806147 16170127666852500505209221)
            ·
              refine ⟨3031898937534843844726729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16170127666852500505209221 3031898937534843844726729)
              ·
                refine ⟨2273924203151132883545047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3031898937534843844726729 2273924203151132883545047)
                ·
                  refine ⟨3410886304726699325317571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2273924203151132883545047 3410886304726699325317571)
                  ·
                    refine ⟨5116329457090048987976357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3410886304726699325317571 5116329457090048987976357)
                    ·
                      refine ⟨959311773204384185245567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5116329457090048987976357 959311773204384185245567)
                      ·
                        rfl

theorem cell23_1868253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_1868253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1868253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1868253 prefixEnd_1868253 := by exact prefixLift 1868253
  have htrace : WordTrace (prefixWord ++ tailWord_1868253) baseStart_1868253 baseEnd_1868253 := by
    simpa [prefixWord, tailWord_1868253, baseEnd_1868253] using wordTrace_append hprefix tailTrace_1868253
  have hstable : (prefixWord ++ tailWord_1868253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868253).length < 2 ^ (prefixWord ++ tailWord_1868253).sum := by decide
  have hdescent : baseEnd_1868253 < baseStart_1868253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868287 : List Nat := [1, 1, 2, 2, 1, 2, 7, 2, 1, 2, 2]
def baseStart_1868287 : Nat := 118140960795 + 1868287 * 2 ^ 59
def prefixEnd_1868287 : Nat := 4983230072969 + 3 ^ 40 * 1868287 * 2
def baseEnd_1868287 : Nat := 959329231546637052220411

theorem tailTrace_1868287 : CollatzResearch.WordTrace tailWord_1868287 prefixEnd_1868287 959329231546637052220411 := by
  unfold tailWord_1868287
  simp only [CollatzResearch.WordTrace]
  refine ⟨68142024982522751861611115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45428016655015167907740743 68142024982522751861611115)
  ·
    refine ⟨102213037473784127792416673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68142024982522751861611115 102213037473784127792416673)
    ·
      refine ⟨76659778105338095844312505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102213037473784127792416673 76659778105338095844312505)
      ·
        refine ⟨57494833579003571883234379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76659778105338095844312505 57494833579003571883234379)
        ·
          refine ⟨86242250368505357824851569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57494833579003571883234379 86242250368505357824851569)
          ·
            refine ⟨64681687776379018368638677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86242250368505357824851569 64681687776379018368638677)
            ·
              refine ⟨1515977057258883243014969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 64681687776379018368638677 1515977057258883243014969)
              ·
                refine ⟨1136982792944162432261227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1515977057258883243014969 1136982792944162432261227)
                ·
                  refine ⟨1705474189416243648391841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1136982792944162432261227 1705474189416243648391841)
                  ·
                    refine ⟨1279105642062182736293881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1705474189416243648391841 1279105642062182736293881)
                    ·
                      refine ⟨959329231546637052220411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1279105642062182736293881 959329231546637052220411)
                      ·
                        rfl

theorem cell23_1868287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7, 2, 1, 2, 2].length) (baseStart_1868287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1868287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1868287 prefixEnd_1868287 := by exact prefixLift 1868287
  have htrace : WordTrace (prefixWord ++ tailWord_1868287) baseStart_1868287 baseEnd_1868287 := by
    simpa [prefixWord, tailWord_1868287, baseEnd_1868287] using wordTrace_append hprefix tailTrace_1868287
  have hstable : (prefixWord ++ tailWord_1868287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868287).length < 2 ^ (prefixWord ++ tailWord_1868287).sum := by decide
  have hdescent : baseEnd_1868287 < baseStart_1868287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868296 : List Nat := [2, 1, 3, 2, 1, 1, 1, 1, 2, 7, 2]
def baseStart_1868296 : Nat := 118140960795 + 1868296 * 2 ^ 59
def prefixEnd_1868296 : Nat := 4983230072969 + 3 ^ 40 * 1868296 * 2
def baseEnd_1868296 : Nat := 959333852872527517007869

theorem tailTrace_1868296 : CollatzResearch.WordTrace tailWord_1868296 prefixEnd_1868296 959333852872527517007869 := by
  unfold tailWord_1868296
  simp only [CollatzResearch.WordTrace]
  refine ⟨34071176619745073199344371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45428235492993430932459161 34071176619745073199344371)
  ·
    refine ⟨51106764929617609799016557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34071176619745073199344371 51106764929617609799016557)
    ·
      refine ⟨19165036848606603674631209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51106764929617609799016557 19165036848606603674631209)
      ·
        refine ⟨14373777636454952755973407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19165036848606603674631209 14373777636454952755973407)
        ·
          refine ⟨21560666454682429133960111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14373777636454952755973407 21560666454682429133960111)
          ·
            refine ⟨32340999682023643700940167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21560666454682429133960111 32340999682023643700940167)
            ·
              refine ⟨48511499523035465551410251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32340999682023643700940167 48511499523035465551410251)
              ·
                refine ⟨72767249284553198327115377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48511499523035465551410251 72767249284553198327115377)
                ·
                  refine ⟨54575436963414898745336533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72767249284553198327115377 54575436963414898745336533)
                  ·
                    refine ⟨1279111803830036689343825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54575436963414898745336533 1279111803830036689343825)
                    ·
                      refine ⟨959333852872527517007869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1279111803830036689343825 959333852872527517007869)
                      ·
                        rfl

theorem cell23_1868296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 2, 7, 2].length) (baseStart_1868296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1868296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1868296 prefixEnd_1868296 := by exact prefixLift 1868296
  have htrace : WordTrace (prefixWord ++ tailWord_1868296) baseStart_1868296 baseEnd_1868296 := by
    simpa [prefixWord, tailWord_1868296, baseEnd_1868296] using wordTrace_append hprefix tailTrace_1868296
  have hstable : (prefixWord ++ tailWord_1868296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868296).length < 2 ^ (prefixWord ++ tailWord_1868296).sum := by decide
  have hdescent : baseEnd_1868296 < baseStart_1868296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868319 : List Nat := [1, 1, 2, 4, 1, 1, 1, 2, 4, 6]
def baseStart_1868319 : Nat := 118140960795 + 1868319 * 2 ^ 59
def prefixEnd_1868319 : Nat := 4983230072969 + 3 ^ 40 * 1868319 * 2
def baseEnd_1868319 : Nat := 319781887642526975673421

theorem tailTrace_1868319 : CollatzResearch.WordTrace tailWord_1868319 prefixEnd_1868319 319781887642526975673421 := by
  unfold tailWord_1868319
  simp only [CollatzResearch.WordTrace]
  refine ⟨68143192118406821326776011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45428794745604547551184007 68143192118406821326776011)
  ·
    refine ⟨102214788177610231990164017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68143192118406821326776011 102214788177610231990164017)
    ·
      refine ⟨76661091133207673992623013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102214788177610231990164017 76661091133207673992623013)
      ·
        refine ⟨14373954587476438873616815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76661091133207673992623013 14373954587476438873616815)
        ·
          refine ⟨21560931881214658310425223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14373954587476438873616815 21560931881214658310425223)
          ·
            refine ⟨32341397821821987465637835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21560931881214658310425223 32341397821821987465637835)
            ·
              refine ⟨48512096732732981198456753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32341397821821987465637835 48512096732732981198456753)
              ·
                refine ⟨36384072549549735898842565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48512096732732981198456753 36384072549549735898842565)
                ·
                  refine ⟨6822013603040575481032981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36384072549549735898842565 6822013603040575481032981)
                  ·
                    refine ⟨319781887642526975673421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6822013603040575481032981 319781887642526975673421)
                    ·
                      rfl

theorem cell23_1868319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4, 6].length) (baseStart_1868319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1868319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1868319 prefixEnd_1868319 := by exact prefixLift 1868319
  have htrace : WordTrace (prefixWord ++ tailWord_1868319) baseStart_1868319 baseEnd_1868319 := by
    simpa [prefixWord, tailWord_1868319, baseEnd_1868319] using wordTrace_append hprefix tailTrace_1868319
  have hstable : (prefixWord ++ tailWord_1868319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868319).length < 2 ^ (prefixWord ++ tailWord_1868319).sum := by decide
  have hdescent : baseEnd_1868319 < baseStart_1868319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868346 : List Nat := [3, 1, 1, 1, 3, 3, 1, 1, 2, 4, 3]
def baseStart_1868346 : Nat := 118140960795 + 1868346 * 2 ^ 59
def prefixEnd_1868346 : Nat := 4983230072969 + 3 ^ 40 * 1868346 * 2
def baseEnd_1868346 : Nat := 959359526905252321382639

theorem tailTrace_1868346 : CollatzResearch.WordTrace tailWord_1868346 prefixEnd_1868346 959359526905252321382639 := by
  unfold tailWord_1868346
  simp only [CollatzResearch.WordTrace]
  refine ⟨17036044222327251234502223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45429451259539336625339261 17036044222327251234502223)
  ·
    refine ⟨25554066333490876851753335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17036044222327251234502223 25554066333490876851753335)
    ·
      refine ⟨38331099500236315277630003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25554066333490876851753335 38331099500236315277630003)
      ·
        refine ⟨57496649250354472916445005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38331099500236315277630003 57496649250354472916445005)
        ·
          refine ⟨21561243468882927343666877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57496649250354472916445005 21561243468882927343666877)
          ·
            refine ⟨8085466300831097753875079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21561243468882927343666877 8085466300831097753875079)
            ·
              refine ⟨12128199451246646630812619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8085466300831097753875079 12128199451246646630812619)
              ·
                refine ⟨18192299176869969946218929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12128199451246646630812619 18192299176869969946218929)
                ·
                  refine ⟨13644224382652477459664197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18192299176869969946218929 13644224382652477459664197)
                  ·
                    refine ⟨2558292071747339523687037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13644224382652477459664197 2558292071747339523687037)
                    ·
                      refine ⟨959359526905252321382639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2558292071747339523687037 959359526905252321382639)
                      ·
                        rfl

theorem cell23_1868346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 2, 4, 3].length) (baseStart_1868346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1868346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1868346 prefixEnd_1868346 := by exact prefixLift 1868346
  have htrace : WordTrace (prefixWord ++ tailWord_1868346) baseStart_1868346 baseEnd_1868346 := by
    simpa [prefixWord, tailWord_1868346, baseEnd_1868346] using wordTrace_append hprefix tailTrace_1868346
  have hstable : (prefixWord ++ tailWord_1868346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868346).length < 2 ^ (prefixWord ++ tailWord_1868346).sum := by decide
  have hdescent : baseEnd_1868346 < baseStart_1868346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868396 : List Nat := [2, 2, 1, 1, 3, 1, 2, 4, 2, 5]
def baseStart_1868396 : Nat := 118140960795 + 1868396 * 2 ^ 59
def prefixEnd_1868396 : Nat := 4983230072969 + 3 ^ 40 * 1868396 * 2
def baseEnd_1868396 : Nat := 319795066979325708585803

theorem tailTrace_1868396 : CollatzResearch.WordTrace tailWord_1868396 prefixEnd_1868396 319795066979325708585803 := by
  unfold tailWord_1868396
  simp only [CollatzResearch.WordTrace]
  refine ⟨34073000269563931738664521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45430667026085242318219361 34073000269563931738664521)
  ·
    refine ⟨25554750202172948803998391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34073000269563931738664521 25554750202172948803998391)
    ·
      refine ⟨38332125303259423205997587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25554750202172948803998391 38332125303259423205997587)
      ·
        refine ⟨57498187954889134808996381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38332125303259423205997587 57498187954889134808996381)
        ·
          refine ⟨21561820483083425553373643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57498187954889134808996381 21561820483083425553373643)
          ·
            refine ⟨32342730724625138330060465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21561820483083425553373643 32342730724625138330060465)
            ·
              refine ⟨24257048043468853747545349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32342730724625138330060465 24257048043468853747545349)
              ·
                refine ⟨4548196508150410077664753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24257048043468853747545349 4548196508150410077664753)
                ·
                  refine ⟨3411147381112807558248565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4548196508150410077664753 3411147381112807558248565)
                  ·
                    refine ⟨319795066979325708585803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3411147381112807558248565 319795066979325708585803)
                    ·
                      rfl

theorem cell23_1868396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 5].length) (baseStart_1868396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1868396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1868396 prefixEnd_1868396 := by exact prefixLift 1868396
  have htrace : WordTrace (prefixWord ++ tailWord_1868396) baseStart_1868396 baseEnd_1868396 := by
    simpa [prefixWord, tailWord_1868396, baseEnd_1868396] using wordTrace_append hprefix tailTrace_1868396
  have hstable : (prefixWord ++ tailWord_1868396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868396).length < 2 ^ (prefixWord ++ tailWord_1868396).sum := by decide
  have hdescent : baseEnd_1868396 < baseStart_1868396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868416 : List Nat := [2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 4]
def baseStart_1868416 : Nat := 118140960795 + 1868416 * 2 ^ 59
def prefixEnd_1868416 : Nat := 4983230072969 + 3 ^ 40 * 1868416 * 2
def baseEnd_1868416 : Nat := 959395470551067047507317

theorem tailTrace_1868416 : CollatzResearch.WordTrace tailWord_1868416 prefixEnd_1868416 959395470551067047507317 := by
  unfold tailWord_1868416
  simp only [CollatzResearch.WordTrace]
  refine ⟨34073364999527703446528551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45431153332703604595371401 34073364999527703446528551)
  ·
    refine ⟨51110047499291555169792827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34073364999527703446528551 51110047499291555169792827)
    ·
      refine ⟨76665071248937332754689241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51110047499291555169792827 76665071248937332754689241)
      ·
        refine ⟨57498803436702999566016931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76665071248937332754689241 57498803436702999566016931)
        ·
          refine ⟨86248205155054499349025397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57498803436702999566016931 86248205155054499349025397)
          ·
            refine ⟨8085769233286359313971131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86248205155054499349025397 8085769233286359313971131)
            ·
              refine ⟨12128653849929538970956697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8085769233286359313971131 12128653849929538970956697)
              ·
                refine ⟨9096490387447154228217523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12128653849929538970956697 9096490387447154228217523)
                ·
                  refine ⟨13644735581170731342326285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9096490387447154228217523 13644735581170731342326285)
                  ·
                    refine ⟨5116775842939024253372357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13644735581170731342326285 5116775842939024253372357)
                    ·
                      refine ⟨959395470551067047507317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5116775842939024253372357 959395470551067047507317)
                      ·
                        rfl

theorem cell23_1868416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 4].length) (baseStart_1868416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1868416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1868416 prefixEnd_1868416 := by exact prefixLift 1868416
  have htrace : WordTrace (prefixWord ++ tailWord_1868416) baseStart_1868416 baseEnd_1868416 := by
    simpa [prefixWord, tailWord_1868416, baseEnd_1868416] using wordTrace_append hprefix tailTrace_1868416
  have hstable : (prefixWord ++ tailWord_1868416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868416).length < 2 ^ (prefixWord ++ tailWord_1868416).sum := by decide
  have hdescent : baseEnd_1868416 < baseStart_1868416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868523 : List Nat := [1, 1, 1, 1, 2, 4, 1, 2, 2, 6, 2]
def baseStart_1868523 : Nat := 118140960795 + 1868523 * 2 ^ 59
def prefixEnd_1868523 : Nat := 4983230072969 + 3 ^ 40 * 1868523 * 2
def baseEnd_1868523 : Nat := 959450412981098128869325

theorem tailTrace_1868523 : CollatzResearch.WordTrace tailWord_1868523 prefixEnd_1868523 959450412981098128869325 := by
  unfold tailWord_1868523
  simp only [CollatzResearch.WordTrace]
  refine ⟨68150632609667764167202223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45433755073111842778134815 68150632609667764167202223)
  ·
    refine ⟨102225948914501646250803335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68150632609667764167202223 102225948914501646250803335)
    ·
      refine ⟨153338923371752469376205003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102225948914501646250803335 153338923371752469376205003)
      ·
        refine ⟨230008385057628704064307505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153338923371752469376205003 230008385057628704064307505)
        ·
          refine ⟨172506288793221528048230629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230008385057628704064307505 172506288793221528048230629)
          ·
            refine ⟨32344929148729036509043243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172506288793221528048230629 32344929148729036509043243)
            ·
              refine ⟨48517393723093554763564865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32344929148729036509043243 48517393723093554763564865)
              ·
                refine ⟨36388045292320166072673649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48517393723093554763564865 36388045292320166072673649)
                ·
                  refine ⟨27291033969240124554505237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36388045292320166072673649 27291033969240124554505237)
                  ·
                    refine ⟨1279267217308130838492433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27291033969240124554505237 1279267217308130838492433)
                    ·
                      refine ⟨959450412981098128869325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1279267217308130838492433 959450412981098128869325)
                      ·
                        rfl

theorem cell23_1868523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 6, 2].length) (baseStart_1868523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1868523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1868523 prefixEnd_1868523 := by exact prefixLift 1868523
  have htrace : WordTrace (prefixWord ++ tailWord_1868523) baseStart_1868523 baseEnd_1868523 := by
    simpa [prefixWord, tailWord_1868523, baseEnd_1868523] using wordTrace_append hprefix tailTrace_1868523
  have hstable : (prefixWord ++ tailWord_1868523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868523).length < 2 ^ (prefixWord ++ tailWord_1868523).sum := by decide
  have hdescent : baseEnd_1868523 < baseStart_1868523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868553 : List Nat := [1, 2, 1, 1, 3, 2, 4, 2, 1, 2, 4]
def baseStart_1868553 : Nat := 118140960795 + 1868553 * 2 ^ 59
def prefixEnd_1868553 : Nat := 4983230072969 + 3 ^ 40 * 1868553 * 2
def baseEnd_1868553 : Nat := 959465817400733011494187

theorem tailTrace_1868553 : CollatzResearch.WordTrace tailWord_1868553 prefixEnd_1868553 959465817400733011494187 := by
  unfold tailWord_1868553
  simp only [CollatzResearch.WordTrace]
  refine ⟨68151726799559079290794313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45434484533039386193862875 68151726799559079290794313)
  ·
    refine ⟨51113795099669309468095735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68151726799559079290794313 51113795099669309468095735)
    ·
      refine ⟨76670692649503964202143603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51113795099669309468095735 76670692649503964202143603)
      ·
        refine ⟨115006038974255946303215405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76670692649503964202143603 115006038974255946303215405)
        ·
          refine ⟨43127264615345979863705777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115006038974255946303215405 43127264615345979863705777)
          ·
            refine ⟨32345448461509484897779333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43127264615345979863705777 32345448461509484897779333)
            ·
              refine ⟨6064771586533028418333625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32345448461509484897779333 6064771586533028418333625)
              ·
                refine ⟨4548578689899771313750219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6064771586533028418333625 4548578689899771313750219)
                ·
                  refine ⟨6822868034849656970625329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4548578689899771313750219 6822868034849656970625329)
                  ·
                    refine ⟨5117151026137242727968997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6822868034849656970625329 5117151026137242727968997)
                    ·
                      refine ⟨959465817400733011494187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5117151026137242727968997 959465817400733011494187)
                      ·
                        rfl

theorem cell23_1868553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 2, 1, 2, 4].length) (baseStart_1868553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1868553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1868553 prefixEnd_1868553 := by exact prefixLift 1868553
  have htrace : WordTrace (prefixWord ++ tailWord_1868553) baseStart_1868553 baseEnd_1868553 := by
    simpa [prefixWord, tailWord_1868553, baseEnd_1868553] using wordTrace_append hprefix tailTrace_1868553
  have hstable : (prefixWord ++ tailWord_1868553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868553).length < 2 ^ (prefixWord ++ tailWord_1868553).sum := by decide
  have hdescent : baseEnd_1868553 < baseStart_1868553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868614 : List Nat := [6, 1, 1, 2, 3, 1, 9]
def baseStart_1868614 : Nat := 118140960795 + 1868614 * 2 ^ 59
def prefixEnd_1868614 : Nat := 4983230072969 + 3 ^ 40 * 1868614 * 2
def baseEnd_1868614 : Nat := 11845643700255028059647

theorem tailTrace_1868614 : CollatzResearch.WordTrace tailWord_1868614 prefixEnd_1868614 11845643700255028059647 := by
  unfold tailWord_1868614
  simp only [CollatzResearch.WordTrace]
  refine ⟨2129810989135565209648903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 45435967768225391139176597 2129810989135565209648903)
  ·
    refine ⟨3194716483703347814473355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2129810989135565209648903 3194716483703347814473355)
    ·
      refine ⟨4792074725555021721710033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3194716483703347814473355 4792074725555021721710033)
      ·
        refine ⟨3594056044166266291282525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4792074725555021721710033 3594056044166266291282525)
        ·
          refine ⟨1347771016562349859230947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3594056044166266291282525 1347771016562349859230947)
          ·
            refine ⟨2021656524843524788846421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1347771016562349859230947 2021656524843524788846421)
            ·
              refine ⟨11845643700255028059647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2021656524843524788846421 11845643700255028059647)
              ·
                rfl

theorem cell23_1868614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 9].length) (baseStart_1868614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1868614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1868614 prefixEnd_1868614 := by exact prefixLift 1868614
  have htrace : WordTrace (prefixWord ++ tailWord_1868614) baseStart_1868614 baseEnd_1868614 := by
    simpa [prefixWord, tailWord_1868614, baseEnd_1868614] using wordTrace_append hprefix tailTrace_1868614
  have hstable : (prefixWord ++ tailWord_1868614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868614).length < 2 ^ (prefixWord ++ tailWord_1868614).sum := by decide
  have hdescent : baseEnd_1868614 < baseStart_1868614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868617 : List Nat := [1, 2, 1, 1, 2, 5, 2, 3, 1, 3, 2]
def baseStart_1868617 : Nat := 118140960795 + 1868617 * 2 ^ 59
def prefixEnd_1868617 : Nat := 4983230072969 + 3 ^ 40 * 1868617 * 2
def baseEnd_1868617 : Nat := 959498680162620761093893

theorem tailTrace_1868617 : CollatzResearch.WordTrace tailWord_1868617 prefixEnd_1868617 959498680162620761093893 := by
  unfold tailWord_1868617
  simp only [CollatzResearch.WordTrace]
  refine ⟨68154061071327218221124105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45436040714218145480749403 68154061071327218221124105)
  ·
    refine ⟨51115545803495413665843079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68154061071327218221124105 51115545803495413665843079)
    ·
      refine ⟨76673318705243120498764619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51115545803495413665843079 76673318705243120498764619)
      ·
        refine ⟨115009978057864680748146929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76673318705243120498764619 115009978057864680748146929)
        ·
          refine ⟨86257483543398510561110197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115009978057864680748146929 86257483543398510561110197)
          ·
            refine ⟨8086639082193610365104081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86257483543398510561110197 8086639082193610365104081)
            ·
              refine ⟨6064979311645207773828061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8086639082193610365104081 6064979311645207773828061)
              ·
                refine ⟨2274367241866952915185523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6064979311645207773828061 2274367241866952915185523)
                ·
                  refine ⟨3411550862800429372778285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2274367241866952915185523 3411550862800429372778285)
                  ·
                    refine ⟨1279331573550161014791857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3411550862800429372778285 1279331573550161014791857)
                    ·
                      refine ⟨959498680162620761093893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1279331573550161014791857 959498680162620761093893)
                      ·
                        rfl

theorem cell23_1868617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 3, 1, 3, 2].length) (baseStart_1868617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1868617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1868617 prefixEnd_1868617 := by exact prefixLift 1868617
  have htrace : WordTrace (prefixWord ++ tailWord_1868617) baseStart_1868617 baseEnd_1868617 := by
    simpa [prefixWord, tailWord_1868617, baseEnd_1868617] using wordTrace_append hprefix tailTrace_1868617
  have hstable : (prefixWord ++ tailWord_1868617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868617).length < 2 ^ (prefixWord ++ tailWord_1868617).sum := by decide
  have hdescent : baseEnd_1868617 < baseStart_1868617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868653 : List Nat := [1, 5, 1, 1, 1, 1, 1, 3, 9]
def baseStart_1868653 : Nat := 118140960795 + 1868653 * 2 ^ 59
def prefixEnd_1868653 : Nat := 4983230072969 + 3 ^ 40 * 1868653 * 2
def baseEnd_1868653 : Nat := 106613018385131402249303

theorem tailTrace_1868653 : CollatzResearch.WordTrace tailWord_1868653 prefixEnd_1868653 106613018385131402249303 := by
  unfold tailWord_1868653
  simp only [CollatzResearch.WordTrace]
  refine ⟨68155374099196796369434613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45436916066131197579623075 68155374099196796369434613)
  ·
    refine ⟨6389566321799699659634495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68155374099196796369434613 6389566321799699659634495)
    ·
      refine ⟨9584349482699549489451743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6389566321799699659634495 9584349482699549489451743)
      ·
        refine ⟨14376524224049324234177615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9584349482699549489451743 14376524224049324234177615)
        ·
          refine ⟨21564786336073986351266423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14376524224049324234177615 21564786336073986351266423)
          ·
            refine ⟨32347179504110979526899635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21564786336073986351266423 32347179504110979526899635)
            ·
              refine ⟨48520769256166469290349453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32347179504110979526899635 48520769256166469290349453)
              ·
                refine ⟨18195288471062425983881045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48520769256166469290349453 18195288471062425983881045)
                ·
                  refine ⟨106613018385131402249303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 18195288471062425983881045 106613018385131402249303)
                  ·
                    rfl

theorem cell23_1868653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 9].length) (baseStart_1868653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1868653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1868653 prefixEnd_1868653 := by exact prefixLift 1868653
  have htrace : WordTrace (prefixWord ++ tailWord_1868653) baseStart_1868653 baseEnd_1868653 := by
    simpa [prefixWord, tailWord_1868653, baseEnd_1868653] using wordTrace_append hprefix tailTrace_1868653
  have hstable : (prefixWord ++ tailWord_1868653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868653).length < 2 ^ (prefixWord ++ tailWord_1868653).sum := by decide
  have hdescent : baseEnd_1868653 < baseStart_1868653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868694 : List Nat := [5, 3, 1, 1, 1, 1, 1, 1, 1, 4, 4]
def baseStart_1868694 : Nat := 118140960795 + 1868694 * 2 ^ 59
def prefixEnd_1868694 : Nat := 4983230072969 + 3 ^ 40 * 1868694 * 2
def baseEnd_1868694 : Nat := 959538218173016959831039

theorem tailTrace_1868694 : CollatzResearch.WordTrace tailWord_1868694 prefixEnd_1868694 959538218173016959831039 := by
  unfold tailWord_1868694
  simp only [CollatzResearch.WordTrace]
  refine ⟨4259804343253016273229821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45437912994698840247784757 4259804343253016273229821)
  ·
    refine ⟨1597426628719881102461183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4259804343253016273229821 1597426628719881102461183)
    ·
      refine ⟨2396139943079821653691775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1597426628719881102461183 2396139943079821653691775)
      ·
        refine ⟨3594209914619732480537663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2396139943079821653691775 3594209914619732480537663)
        ·
          refine ⟨5391314871929598720806495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3594209914619732480537663 5391314871929598720806495)
          ·
            refine ⟨8086972307894398081209743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5391314871929598720806495 8086972307894398081209743)
            ·
              refine ⟨12130458461841597121814615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8086972307894398081209743 12130458461841597121814615)
              ·
                refine ⟨18195687692762395682721923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12130458461841597121814615 18195687692762395682721923)
                ·
                  refine ⟨27293531539143593524082885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18195687692762395682721923 27293531539143593524082885)
                  ·
                    refine ⟨5117537163589423785765541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27293531539143593524082885 5117537163589423785765541)
                    ·
                      refine ⟨959538218173016959831039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5117537163589423785765541 959538218173016959831039)
                      ·
                        rfl

theorem cell23_1868694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_1868694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1868694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1868694 prefixEnd_1868694 := by exact prefixLift 1868694
  have htrace : WordTrace (prefixWord ++ tailWord_1868694) baseStart_1868694 baseEnd_1868694 := by
    simpa [prefixWord, tailWord_1868694, baseEnd_1868694] using wordTrace_append hprefix tailTrace_1868694
  have hstable : (prefixWord ++ tailWord_1868694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868694).length < 2 ^ (prefixWord ++ tailWord_1868694).sum := by decide
  have hdescent : baseEnd_1868694 < baseStart_1868694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868723 : List Nat := [1, 1, 1, 2, 3, 1, 2, 2, 2, 3, 5]
def baseStart_1868723 : Nat := 118140960795 + 1868723 * 2 ^ 59
def prefixEnd_1868723 : Nat := 4983230072969 + 3 ^ 40 * 1868723 * 2
def baseEnd_1868723 : Nat := 959553109111997346368405

theorem tailTrace_1868723 : CollatzResearch.WordTrace tailWord_1868723 prefixEnd_1868723 959553109111997346368405 := by
  unfold tailWord_1868723
  simp only [CollatzResearch.WordTrace]
  refine ⟨68157927208943198324482823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45438618139295465549655215 68157927208943198324482823)
  ·
    refine ⟨102236890813414797486724235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68157927208943198324482823 102236890813414797486724235)
    ·
      refine ⟨153355336220122196230086353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102236890813414797486724235 153355336220122196230086353)
      ·
        refine ⟨115016502165091647172564765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153355336220122196230086353 115016502165091647172564765)
        ·
          refine ⟨43131188311909367689711787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115016502165091647172564765 43131188311909367689711787)
          ·
            refine ⟨64696782467864051534567681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43131188311909367689711787 64696782467864051534567681)
            ·
              refine ⟨48522586850898038650925761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64696782467864051534567681 48522586850898038650925761)
              ·
                refine ⟨36391940138173528988194321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48522586850898038650925761 36391940138173528988194321)
                ·
                  refine ⟨27293955103630146741145741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36391940138173528988194321 27293955103630146741145741)
                  ·
                    refine ⟨10235233163861305027929653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27293955103630146741145741 10235233163861305027929653)
                    ·
                      refine ⟨959553109111997346368405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10235233163861305027929653 959553109111997346368405)
                      ·
                        rfl

theorem cell23_1868723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3, 5].length) (baseStart_1868723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1868723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1868723 prefixEnd_1868723 := by exact prefixLift 1868723
  have htrace : WordTrace (prefixWord ++ tailWord_1868723) baseStart_1868723 baseEnd_1868723 := by
    simpa [prefixWord, tailWord_1868723, baseEnd_1868723] using wordTrace_append hprefix tailTrace_1868723
  have hstable : (prefixWord ++ tailWord_1868723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868723).length < 2 ^ (prefixWord ++ tailWord_1868723).sum := by decide
  have hdescent : baseEnd_1868723 < baseStart_1868723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868730 : List Nat := [3, 1, 1, 1, 2, 1, 3, 2, 5, 4]
def baseStart_1868730 : Nat := 118140960795 + 1868730 * 2 ^ 59
def prefixEnd_1868730 : Nat := 4983230072969 + 3 ^ 40 * 1868730 * 2
def baseEnd_1868730 : Nat := 319852234492192939660291

theorem tailTrace_1868730 : CollatzResearch.WordTrace tailWord_1868730 prefixEnd_1868730 319852234492192939660291 := by
  unfold tailWord_1868730
  simp only [CollatzResearch.WordTrace]
  refine ⟨17039545629979459629996911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45438788346611892346658429 17039545629979459629996911)
  ·
    refine ⟨25559318444969189444995367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17039545629979459629996911 25559318444969189444995367)
    ·
      refine ⟨38338977667453784167493051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25559318444969189444995367 38338977667453784167493051)
      ·
        refine ⟨57508466501180676251239577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38338977667453784167493051 57508466501180676251239577)
        ·
          refine ⟨43131349875885507188429683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57508466501180676251239577 43131349875885507188429683)
          ·
            refine ⟨64697024813828260782644525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43131349875885507188429683 64697024813828260782644525)
            ·
              refine ⟨24261384305185597793491697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64697024813828260782644525 24261384305185597793491697)
              ·
                refine ⟨18196038228889198345118773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24261384305185597793491697 18196038228889198345118773)
                ·
                  refine ⟨1705878583958362344854885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18196038228889198345118773 1705878583958362344854885)
                  ·
                    refine ⟨319852234492192939660291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1705878583958362344854885 319852234492192939660291)
                    ·
                      rfl

theorem cell23_1868730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 5, 4].length) (baseStart_1868730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1868730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1868730 prefixEnd_1868730 := by exact prefixLift 1868730
  have htrace : WordTrace (prefixWord ++ tailWord_1868730) baseStart_1868730 baseEnd_1868730 := by
    simpa [prefixWord, tailWord_1868730, baseEnd_1868730] using wordTrace_append hprefix tailTrace_1868730
  have hstable : (prefixWord ++ tailWord_1868730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868730).length < 2 ^ (prefixWord ++ tailWord_1868730).sum := by decide
  have hdescent : baseEnd_1868730 < baseStart_1868730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868747 : List Nat := [1, 1, 1, 1, 3, 6, 2, 1, 3, 4]
def baseStart_1868747 : Nat := 118140960795 + 1868747 * 2 ^ 59
def prefixEnd_1868747 : Nat := 4983230072969 + 3 ^ 40 * 1868747 * 2
def baseEnd_1868747 : Nat := 319855144215901750822765

theorem tailTrace_1868747 : CollatzResearch.WordTrace tailWord_1868747 prefixEnd_1868747 319855144215901750822765 := by
  unfold tailWord_1868747
  simp only [CollatzResearch.WordTrace]
  refine ⟨68158802560856250423356495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45439201707237500282237663 68158802560856250423356495)
  ·
    refine ⟨102238203841284375635034743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68158802560856250423356495 102238203841284375635034743)
    ·
      refine ⟨153357305761926563452552115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102238203841284375635034743 153357305761926563452552115)
      ·
        refine ⟨230035958642889845178828173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153357305761926563452552115 230035958642889845178828173)
        ·
          refine ⟨86263484491083691942060565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230035958642889845178828173 86263484491083691942060565)
          ·
            refine ⟨4043600835519548059784089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 86263484491083691942060565 4043600835519548059784089)
            ·
              refine ⟨3032700626639661044838067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4043600835519548059784089 3032700626639661044838067)
              ·
                refine ⟨4549050939959491567257101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3032700626639661044838067 4549050939959491567257101)
                ·
                  refine ⟨1705894102484809337721413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4549050939959491567257101 1705894102484809337721413)
                  ·
                    refine ⟨319855144215901750822765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1705894102484809337721413 319855144215901750822765)
                    ·
                      rfl

theorem cell23_1868747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 1, 3, 4].length) (baseStart_1868747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1868747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1868747 prefixEnd_1868747 := by exact prefixLift 1868747
  have htrace : WordTrace (prefixWord ++ tailWord_1868747) baseStart_1868747 baseEnd_1868747 := by
    simpa [prefixWord, tailWord_1868747, baseEnd_1868747] using wordTrace_append hprefix tailTrace_1868747
  have hstable : (prefixWord ++ tailWord_1868747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868747).length < 2 ^ (prefixWord ++ tailWord_1868747).sum := by decide
  have hdescent : baseEnd_1868747 < baseStart_1868747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868754 : List Nat := [3, 2, 2, 3, 1, 1, 2, 1, 2, 4, 2]
def baseStart_1868754 : Nat := 118140960795 + 1868754 * 2 ^ 59
def prefixEnd_1868754 : Nat := 4983230072969 + 3 ^ 40 * 1868754 * 2
def baseEnd_1868754 : Nat := 959569027012286725080763

theorem tailTrace_1868754 : CollatzResearch.WordTrace tailWord_1868754 prefixEnd_1868754 959569027012286725080763 := by
  unfold tailWord_1868754
  simp only [CollatzResearch.WordTrace]
  refine ⟨17039764467957722654715329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45439371914553927079240877 17039764467957722654715329)
  ·
    refine ⟨12779823350968291991036497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17039764467957722654715329 12779823350968291991036497)
    ·
      refine ⟨9584867513226218993277373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12779823350968291991036497 9584867513226218993277373)
      ·
        refine ⟨3594325317459832122479015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9584867513226218993277373 3594325317459832122479015)
        ·
          refine ⟨5391487976189748183718523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3594325317459832122479015 5391487976189748183718523)
          ·
            refine ⟨8087231964284622275577785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5391487976189748183718523 8087231964284622275577785)
            ·
              refine ⟨6065423973213466706683339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8087231964284622275577785 6065423973213466706683339)
              ·
                refine ⟨9098135959820200060025009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6065423973213466706683339 9098135959820200060025009)
                ·
                  refine ⟨6823601969865150045018757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9098135959820200060025009 6823601969865150045018757)
                  ·
                    refine ⟨1279425369349715633441017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6823601969865150045018757 1279425369349715633441017)
                    ·
                      refine ⟨959569027012286725080763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1279425369349715633441017 959569027012286725080763)
                      ·
                        rfl

theorem cell23_1868754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_1868754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1868754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1868754 prefixEnd_1868754 := by exact prefixLift 1868754
  have htrace : WordTrace (prefixWord ++ tailWord_1868754) baseStart_1868754 baseEnd_1868754 := by
    simpa [prefixWord, tailWord_1868754, baseEnd_1868754] using wordTrace_append hprefix tailTrace_1868754
  have hstable : (prefixWord ++ tailWord_1868754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868754).length < 2 ^ (prefixWord ++ tailWord_1868754).sum := by decide
  have hdescent : baseEnd_1868754 < baseStart_1868754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868798 : List Nat := [4, 2, 2, 2, 3, 1, 1, 1, 3, 4]
def baseStart_1868798 : Nat := 118140960795 + 1868798 * 2 ^ 59
def prefixEnd_1868798 : Nat := 4983230072969 + 3 ^ 40 * 1868798 * 2
def baseEnd_1868798 : Nat := 319863873387028184310187

theorem tailTrace_1868798 : CollatzResearch.WordTrace tailWord_1868798 prefixEnd_1868798 319863873387028184310187 := by
  unfold tailWord_1868798
  simp only [CollatzResearch.WordTrace]
  refine ⟨8520082835458935766682881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45440441789114324088975365 8520082835458935766682881)
  ·
    refine ⟨6390062126594201825012161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8520082835458935766682881 6390062126594201825012161)
    ·
      refine ⟨4792546594945651368759121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6390062126594201825012161 4792546594945651368759121)
      ·
        refine ⟨3594409946209238526569341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4792546594945651368759121 3594409946209238526569341)
        ·
          refine ⟨1347903729828464447463503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3594409946209238526569341 1347903729828464447463503)
          ·
            refine ⟨2021855594742696671195255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1347903729828464447463503 2021855594742696671195255)
            ·
              refine ⟨3032783392114045006792883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2021855594742696671195255 3032783392114045006792883)
              ·
                refine ⟨4549175088171067510189325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3032783392114045006792883 4549175088171067510189325)
                ·
                  refine ⟨1705940658064150316320997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4549175088171067510189325 1705940658064150316320997)
                  ·
                    refine ⟨319863873387028184310187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1705940658064150316320997 319863873387028184310187)
                    ·
                      rfl

theorem cell23_1868798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_1868798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1868798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1868798 prefixEnd_1868798 := by exact prefixLift 1868798
  have htrace : WordTrace (prefixWord ++ tailWord_1868798) baseStart_1868798 baseEnd_1868798 := by
    simpa [prefixWord, tailWord_1868798, baseEnd_1868798] using wordTrace_append hprefix tailTrace_1868798
  have hstable : (prefixWord ++ tailWord_1868798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868798).length < 2 ^ (prefixWord ++ tailWord_1868798).sum := by decide
  have hdescent : baseEnd_1868798 < baseStart_1868798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868824 : List Nat := [2, 1, 2, 3, 2, 4, 1, 2, 1, 5]
def baseStart_1868824 : Nat := 118140960795 + 1868824 * 2 ^ 59
def prefixEnd_1868824 : Nat := 4983230072969 + 3 ^ 40 * 1868824 * 2
def baseEnd_1868824 : Nat := 319868323552700483735147

theorem tailTrace_1868824 : CollatzResearch.WordTrace tailWord_1868824 prefixEnd_1868824 319868323552700483735147 := by
  unfold tailWord_1868824
  simp only [CollatzResearch.WordTrace]
  refine ⟨34080805490788646286954763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45441073987718195049273017 34080805490788646286954763)
  ·
    refine ⟨51121208236182969430432145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34080805490788646286954763 51121208236182969430432145)
    ·
      refine ⟨38340906177137227072824109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51121208236182969430432145 38340906177137227072824109)
      ·
        refine ⟨14377839816426460152309041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38340906177137227072824109 14377839816426460152309041)
        ·
          refine ⟨10783379862319845114231781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14377839816426460152309041 10783379862319845114231781)
          ·
            refine ⟨2021883724184970958918459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10783379862319845114231781 2021883724184970958918459)
            ·
              refine ⟨3032825586277456438377689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2021883724184970958918459 3032825586277456438377689)
              ·
                refine ⟨2274619189708092328783267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3032825586277456438377689 2274619189708092328783267)
                ·
                  refine ⟨3411928784562138493174901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2274619189708092328783267 3411928784562138493174901)
                  ·
                    refine ⟨319868323552700483735147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3411928784562138493174901 319868323552700483735147)
                    ·
                      rfl

theorem cell23_1868824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 2, 1, 5].length) (baseStart_1868824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1868824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1868824 prefixEnd_1868824 := by exact prefixLift 1868824
  have htrace : WordTrace (prefixWord ++ tailWord_1868824) baseStart_1868824 baseEnd_1868824 := by
    simpa [prefixWord, tailWord_1868824, baseEnd_1868824] using wordTrace_append hprefix tailTrace_1868824
  have hstable : (prefixWord ++ tailWord_1868824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868824).length < 2 ^ (prefixWord ++ tailWord_1868824).sum := by decide
  have hdescent : baseEnd_1868824 < baseStart_1868824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868844 : List Nat := [2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 4]
def baseStart_1868844 : Nat := 118140960795 + 1868844 * 2 ^ 59
def prefixEnd_1868844 : Nat := 4983230072969 + 3 ^ 40 * 1868844 * 2
def baseEnd_1868844 : Nat := 959615240271191372955349

theorem tailTrace_1868844 : CollatzResearch.WordTrace tailWord_1868844 prefixEnd_1868844 959615240271191372955349 := by
  unfold tailWord_1868844
  simp only [CollatzResearch.WordTrace]
  refine ⟨34081170220752417994818793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45441560294336557326425057 34081170220752417994818793)
  ·
    refine ⟨25560877665564313496114095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34081170220752417994818793 25560877665564313496114095)
    ·
      refine ⟨38341316498346470244171143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25560877665564313496114095 38341316498346470244171143)
      ·
        refine ⟨57511974747519705366256715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38341316498346470244171143 57511974747519705366256715)
        ·
          refine ⟨86267962121279558049385073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57511974747519705366256715 86267962121279558049385073)
          ·
            refine ⟨64700971590959668537038805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86267962121279558049385073 64700971590959668537038805)
            ·
              refine ⟨1516429021663117231336847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 64700971590959668537038805 1516429021663117231336847)
              ·
                refine ⟨2274643532494675847005271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1516429021663117231336847 2274643532494675847005271)
                ·
                  refine ⟨3411965298742013770507907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2274643532494675847005271 3411965298742013770507907)
                  ·
                    refine ⟨5117947948113020655761861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3411965298742013770507907 5117947948113020655761861)
                    ·
                      refine ⟨959615240271191372955349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5117947948113020655761861 959615240271191372955349)
                      ·
                        rfl

theorem cell23_1868844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 4].length) (baseStart_1868844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1868844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1868844 prefixEnd_1868844 := by exact prefixLift 1868844
  have htrace : WordTrace (prefixWord ++ tailWord_1868844) baseStart_1868844 baseEnd_1868844 := by
    simpa [prefixWord, tailWord_1868844, baseEnd_1868844] using wordTrace_append hprefix tailTrace_1868844
  have hstable : (prefixWord ++ tailWord_1868844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868844).length < 2 ^ (prefixWord ++ tailWord_1868844).sum := by decide
  have hdescent : baseEnd_1868844 < baseStart_1868844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868898 : List Nat := [3, 3, 2, 2, 1, 1, 4, 1, 1, 2, 3]
def baseStart_1868898 : Nat := 118140960795 + 1868898 * 2 ^ 59
def prefixEnd_1868898 : Nat := 4983230072969 + 3 ^ 40 * 1868898 * 2
def baseEnd_1868898 : Nat := 959642968226534161680101

theorem tailTrace_1868898 : CollatzResearch.WordTrace tailWord_1868898 prefixEnd_1868898 959642968226534161680101 := by
  unfold tailWord_1868898
  simp only [CollatzResearch.WordTrace]
  refine ⟨17041077495827300803025837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45442873322206135474735565 17041077495827300803025837)
  ·
    refine ⟨6390404060935237801134689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17041077495827300803025837 6390404060935237801134689)
    ·
      refine ⟨4792803045701428350851017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6390404060935237801134689 4792803045701428350851017)
      ·
        refine ⟨3594602284276071263138263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4792803045701428350851017 3594602284276071263138263)
        ·
          refine ⟨5391903426414106894707395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3594602284276071263138263 5391903426414106894707395)
          ·
            refine ⟨8087855139621160342061093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5391903426414106894707395 8087855139621160342061093)
            ·
              refine ⟨1516472838678967564136455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8087855139621160342061093 1516472838678967564136455)
              ·
                refine ⟨2274709258018451346204683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1516472838678967564136455 2274709258018451346204683)
                ·
                  refine ⟨3412063887027677019307025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2274709258018451346204683 3412063887027677019307025)
                  ·
                    refine ⟨2559047915270757764480269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3412063887027677019307025 2559047915270757764480269)
                    ·
                      refine ⟨959642968226534161680101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2559047915270757764480269 959642968226534161680101)
                      ·
                        rfl

theorem cell23_1868898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_1868898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1868898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1868898 prefixEnd_1868898 := by exact prefixLift 1868898
  have htrace : WordTrace (prefixWord ++ tailWord_1868898) baseStart_1868898 baseEnd_1868898 := by
    simpa [prefixWord, tailWord_1868898, baseEnd_1868898] using wordTrace_append hprefix tailTrace_1868898
  have hstable : (prefixWord ++ tailWord_1868898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868898).length < 2 ^ (prefixWord ++ tailWord_1868898).sum := by decide
  have hdescent : baseEnd_1868898 < baseStart_1868898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868951 : List Nat := [1, 1, 3, 3, 3, 1, 1, 2, 4, 2, 2]
def baseStart_1868951 : Nat := 118140960795 + 1868951 * 2 ^ 59
def prefixEnd_1868951 : Nat := 4983230072969 + 3 ^ 40 * 1868951 * 2
def baseEnd_1868951 : Nat := 959670182701222454317357

theorem tailTrace_1868951 : CollatzResearch.WordTrace tailWord_1868951 prefixEnd_1868951 959670182701222454317357 := by
  unfold tailWord_1868951
  simp only [CollatzResearch.WordTrace]
  refine ⟨68166243052117193263782707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45444162034744795509188471 68166243052117193263782707)
  ·
    refine ⟨102249364578175789895674061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68166243052117193263782707 102249364578175789895674061)
    ·
      refine ⟨38343511716815921210877773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102249364578175789895674061 38343511716815921210877773)
      ·
        refine ⟨14378816893805970454079165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38343511716815921210877773 14378816893805970454079165)
        ·
          refine ⟨5392056335177238920279687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14378816893805970454079165 5392056335177238920279687)
          ·
            refine ⟨8088084502765858380419531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5392056335177238920279687 8088084502765858380419531)
            ·
              refine ⟨12132126754148787570629297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8088084502765858380419531 12132126754148787570629297)
              ·
                refine ⟨9099095065611590677971973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12132126754148787570629297 9099095065611590677971973)
                ·
                  refine ⟨1706080324802173252119745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9099095065611590677971973 1706080324802173252119745)
                  ·
                    refine ⟨1279560243601629939089809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1706080324802173252119745 1279560243601629939089809)
                    ·
                      refine ⟨959670182701222454317357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1279560243601629939089809 959670182701222454317357)
                      ·
                        rfl

theorem cell23_1868951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 4, 2, 2].length) (baseStart_1868951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1868951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1868951 prefixEnd_1868951 := by exact prefixLift 1868951
  have htrace : WordTrace (prefixWord ++ tailWord_1868951) baseStart_1868951 baseEnd_1868951 := by
    simpa [prefixWord, tailWord_1868951, baseEnd_1868951] using wordTrace_append hprefix tailTrace_1868951
  have hstable : (prefixWord ++ tailWord_1868951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868951).length < 2 ^ (prefixWord ++ tailWord_1868951).sum := by decide
  have hdescent : baseEnd_1868951 < baseStart_1868951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
