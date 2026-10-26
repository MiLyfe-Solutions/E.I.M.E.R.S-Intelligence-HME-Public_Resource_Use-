import V185TrunkScan23Chunk0748

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4429582 : List Nat := [4, 1, 1, 2, 1, 1, 2, 3, 1, 3, 4]
def baseStart_4429582 : Nat := 118140960795 + 4429582 * 2 ^ 59
def prefixEnd_4429582 : Nat := 4983230072969 + 3 ^ 40 * 4429582 * 2
def baseEnd_4429582 : Nat := 2274504664504193473753729

theorem tailTrace_4429582 : CollatzResearch.WordTrace tailWord_4429582 prefixEnd_4429582 2274504664504193473753729 := by
  unfold tailWord_4429582
  simp only [CollatzResearch.WordTrace]
  refine ⟨20195016029798550152710375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107706752158925600814455333 20195016029798550152710375)
  ·
    refine ⟨30292524044697825229065563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20195016029798550152710375 30292524044697825229065563)
    ·
      refine ⟨45438786067046737843598345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30292524044697825229065563 45438786067046737843598345)
      ·
        refine ⟨34079089550285053382698759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45438786067046737843598345 34079089550285053382698759)
        ·
          refine ⟨51118634325427580074048139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34079089550285053382698759 51118634325427580074048139)
          ·
            refine ⟨76677951488141370111072209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51118634325427580074048139 76677951488141370111072209)
            ·
              refine ⟨57508463616106027583304157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76677951488141370111072209 57508463616106027583304157)
              ·
                refine ⟨21565673856039760343739059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57508463616106027583304157 21565673856039760343739059)
                ·
                  refine ⟨32348510784059640515608589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21565673856039760343739059 32348510784059640515608589)
                  ·
                    refine ⟨12130691544022365193353221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32348510784059640515608589 12130691544022365193353221)
                    ·
                      refine ⟨2274504664504193473753729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12130691544022365193353221 2274504664504193473753729)
                      ·
                        rfl

theorem cell23_4429582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_4429582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4429582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4429582 prefixEnd_4429582 := by exact prefixLift 4429582
  have htrace : WordTrace (prefixWord ++ tailWord_4429582) baseStart_4429582 baseEnd_4429582 := by
    simpa [prefixWord, tailWord_4429582, baseEnd_4429582] using wordTrace_append hprefix tailTrace_4429582
  have hstable : (prefixWord ++ tailWord_4429582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4429582).length < 2 ^ (prefixWord ++ tailWord_4429582).sum := by decide
  have hdescent : baseEnd_4429582 < baseStart_4429582 := by decide
  rcases family_descends (prefixWord ++ tailWord_4429582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4429595 : List Nat := [1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 6]
def baseStart_4429595 : Nat := 118140960795 + 4429595 * 2 ^ 59
def prefixEnd_4429595 : Nat := 4983230072969 + 3 ^ 40 * 4429595 * 2
def baseEnd_4429595 : Nat := 2274511339752701922891169

theorem tailTrace_4429595 : CollatzResearch.WordTrace tailWord_4429595 prefixEnd_4429595 2274511339752701922891169 := by
  unfold tailWord_4429595
  simp only [CollatzResearch.WordTrace]
  refine ⟨161560602387341304441906239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107707068258227536294604159 161560602387341304441906239)
  ·
    refine ⟨242340903581011956662859359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161560602387341304441906239 242340903581011956662859359)
    ·
      refine ⟨363511355371517934994289039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242340903581011956662859359 363511355371517934994289039)
      ·
        refine ⟨545267033057276902491433559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 363511355371517934994289039 545267033057276902491433559)
        ·
          refine ⟨817900549585915353737150339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 545267033057276902491433559 817900549585915353737150339)
          ·
            refine ⟨1226850824378873030605725509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 817900549585915353737150339 1226850824378873030605725509)
            ·
              refine ⟨230034529571038693238573533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1226850824378873030605725509 230034529571038693238573533)
              ·
                refine ⟨86262948589139509964465075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 230034529571038693238573533 86262948589139509964465075)
                ·
                  refine ⟨129394422883709264946697613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86262948589139509964465075 129394422883709264946697613)
                  ·
                    refine ⟨48522908581390974355011605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 129394422883709264946697613 48522908581390974355011605)
                    ·
                      refine ⟨2274511339752701922891169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48522908581390974355011605 2274511339752701922891169)
                      ·
                        rfl

theorem cell23_4429595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 6].length) (baseStart_4429595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4429595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4429595 prefixEnd_4429595 := by exact prefixLift 4429595
  have htrace : WordTrace (prefixWord ++ tailWord_4429595) baseStart_4429595 baseEnd_4429595 := by
    simpa [prefixWord, tailWord_4429595, baseEnd_4429595] using wordTrace_append hprefix tailTrace_4429595
  have hstable : (prefixWord ++ tailWord_4429595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4429595).length < 2 ^ (prefixWord ++ tailWord_4429595).sum := by decide
  have hdescent : baseEnd_4429595 < baseStart_4429595 := by decide
  rcases family_descends (prefixWord ++ tailWord_4429595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4429599 : List Nat := [1, 1, 2, 4, 2, 1, 2, 2, 2, 4, 2]
def baseStart_4429599 : Nat := 118140960795 + 4429599 * 2 ^ 59
def prefixEnd_4429599 : Nat := 4983230072969 + 3 ^ 40 * 4429599 * 2
def baseEnd_4429599 : Nat := 2274513393675319907241151

theorem tailTrace_4429599 : CollatzResearch.WordTrace tailWord_4429599 prefixEnd_4429599 2274513393675319907241151 := by
  unfold tailWord_4429599
  simp only [CollatzResearch.WordTrace]
  refine ⟨161560748279326813125051851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107707165519551208750034567 161560748279326813125051851)
  ·
    refine ⟨242341122418990219687577777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161560748279326813125051851 242341122418990219687577777)
    ·
      refine ⟨181755841814242664765683333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 242341122418990219687577777 181755841814242664765683333)
      ·
        refine ⟨34079220340170499643565625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 181755841814242664765683333 34079220340170499643565625)
        ·
          refine ⟨25559415255127874732674219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34079220340170499643565625 25559415255127874732674219)
          ·
            refine ⟨38339122882691812099011329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25559415255127874732674219 38339122882691812099011329)
            ·
              refine ⟨28754342162018859074258497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38339122882691812099011329 28754342162018859074258497)
              ·
                refine ⟨21565756621514144305693873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28754342162018859074258497 21565756621514144305693873)
                ·
                  refine ⟨16174317466135608229270405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21565756621514144305693873 16174317466135608229270405)
                  ·
                    refine ⟨3032684524900426542988201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16174317466135608229270405 3032684524900426542988201)
                    ·
                      refine ⟨2274513393675319907241151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3032684524900426542988201 2274513393675319907241151)
                      ·
                        rfl

theorem cell23_4429599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 2, 4, 2].length) (baseStart_4429599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4429599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4429599 prefixEnd_4429599 := by exact prefixLift 4429599
  have htrace : WordTrace (prefixWord ++ tailWord_4429599) baseStart_4429599 baseEnd_4429599 := by
    simpa [prefixWord, tailWord_4429599, baseEnd_4429599] using wordTrace_append hprefix tailTrace_4429599
  have hstable : (prefixWord ++ tailWord_4429599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4429599).length < 2 ^ (prefixWord ++ tailWord_4429599).sum := by decide
  have hdescent : baseEnd_4429599 < baseStart_4429599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4429599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4429602 : List Nat := [3, 3, 1, 1, 2, 1, 1, 1, 2, 3, 5]
def baseStart_4429602 : Nat := 118140960795 + 4429602 * 2 ^ 59
def prefixEnd_4429602 : Nat := 4983230072969 + 3 ^ 40 * 4429602 * 2
def baseEnd_4429602 : Nat := 2274514934117283395503637

theorem tailTrace_4429602 : CollatzResearch.WordTrace tailWord_4429602 prefixEnd_4429602 2274514934117283395503637 := by
  unfold tailWord_4429602
  simp only [CollatzResearch.WordTrace]
  refine ⟨40390214424578986159352765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107707238465543963091607373 40390214424578986159352765)
  ·
    refine ⟨15146330409217119809757287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40390214424578986159352765 15146330409217119809757287)
    ·
      refine ⟨22719495613825679714635931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15146330409217119809757287 22719495613825679714635931)
      ·
        refine ⟨34079243420738519571953897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22719495613825679714635931 34079243420738519571953897)
        ·
          refine ⟨25559432565553889678965423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34079243420738519571953897 25559432565553889678965423)
          ·
            refine ⟨38339148848330834518448135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25559432565553889678965423 38339148848330834518448135)
            ·
              refine ⟨57508723272496251777672203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38339148848330834518448135 57508723272496251777672203)
              ·
                refine ⟨86263084908744377666508305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57508723272496251777672203 86263084908744377666508305)
                ·
                  refine ⟨64697313681558283249881229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86263084908744377666508305 64697313681558283249881229)
                  ·
                    refine ⟨24261492630584356218705461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 64697313681558283249881229 24261492630584356218705461)
                    ·
                      refine ⟨2274514934117283395503637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24261492630584356218705461 2274514934117283395503637)
                      ·
                        rfl

theorem cell23_4429602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_4429602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4429602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4429602 prefixEnd_4429602 := by exact prefixLift 4429602
  have htrace : WordTrace (prefixWord ++ tailWord_4429602) baseStart_4429602 baseEnd_4429602 := by
    simpa [prefixWord, tailWord_4429602, baseEnd_4429602] using wordTrace_append hprefix tailTrace_4429602
  have hstable : (prefixWord ++ tailWord_4429602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4429602).length < 2 ^ (prefixWord ++ tailWord_4429602).sum := by decide
  have hdescent : baseEnd_4429602 < baseStart_4429602 := by decide
  rcases family_descends (prefixWord ++ tailWord_4429602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4429689 : List Nat := [1, 2, 1, 3, 2, 2, 1, 1, 2, 6, 2]
def baseStart_4429689 : Nat := 118140960795 + 4429689 * 2 ^ 59
def prefixEnd_4429689 : Nat := 4983230072969 + 3 ^ 40 * 4429689 * 2
def baseEnd_4429689 : Nat := 2274559606934224555115737

theorem tailTrace_4429689 : CollatzResearch.WordTrace tailWord_4429689 prefixEnd_4429689 2274559606934224555115737 := by
  unfold tailWord_4429689
  simp only [CollatzResearch.WordTrace]
  refine ⟨161564030849000758495828121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107709353899333838997218747 161564030849000758495828121)
  ·
    refine ⟨121173023136750568871871091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161564030849000758495828121 121173023136750568871871091)
    ·
      refine ⟨181759534705125853307806637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121173023136750568871871091 181759534705125853307806637)
      ·
        refine ⟨68159825514422194990427489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 181759534705125853307806637 68159825514422194990427489)
        ·
          refine ⟨51119869135816646242820617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68159825514422194990427489 51119869135816646242820617)
          ·
            refine ⟨38339901851862484682115463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51119869135816646242820617 38339901851862484682115463)
            ·
              refine ⟨57509852777793727023173195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38339901851862484682115463 57509852777793727023173195)
              ·
                refine ⟨86264779166690590534759793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57509852777793727023173195 86264779166690590534759793)
                ·
                  refine ⟨64698584375017942901069845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86264779166690590534759793 64698584375017942901069845)
                  ·
                    refine ⟨3032746142578966073487649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 64698584375017942901069845 3032746142578966073487649)
                    ·
                      refine ⟨2274559606934224555115737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3032746142578966073487649 2274559606934224555115737)
                      ·
                        rfl

theorem cell23_4429689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 6, 2].length) (baseStart_4429689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4429689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4429689 prefixEnd_4429689 := by exact prefixLift 4429689
  have htrace : WordTrace (prefixWord ++ tailWord_4429689) baseStart_4429689 baseEnd_4429689 := by
    simpa [prefixWord, tailWord_4429689, baseEnd_4429689] using wordTrace_append hprefix tailTrace_4429689
  have hstable : (prefixWord ++ tailWord_4429689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4429689).length < 2 ^ (prefixWord ++ tailWord_4429689).sum := by decide
  have hdescent : baseEnd_4429689 < baseStart_4429689 := by decide
  rcases family_descends (prefixWord ++ tailWord_4429689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4429699 : List Nat := [1, 1, 1, 3, 4, 2, 1, 2, 4, 4]
def baseStart_4429699 : Nat := 118140960795 + 4429699 * 2 ^ 59
def prefixEnd_4429699 : Nat := 4983230072969 + 3 ^ 40 * 4429699 * 2
def baseEnd_4429699 : Nat := 758188247246923171996897

theorem tailTrace_4429699 : CollatzResearch.WordTrace tailWord_4429699 prefixEnd_4429699 758188247246923171996897 := by
  unfold tailWord_4429699
  simp only [CollatzResearch.WordTrace]
  refine ⟨161564395578964530203692151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107709597052643020135794767 161564395578964530203692151)
  ·
    refine ⟨242346593368446795305538227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161564395578964530203692151 242346593368446795305538227)
    ·
      refine ⟨363519890052670192958307341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242346593368446795305538227 363519890052670192958307341)
      ·
        refine ⟨136319958769751322359365253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 363519890052670192958307341 136319958769751322359365253)
        ·
          refine ⟨25559992269328372942380985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 136319958769751322359365253 25559992269328372942380985)
          ·
            refine ⟨19169994201996279706785739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25559992269328372942380985 19169994201996279706785739)
            ·
              refine ⟨28754991302994419560178609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19169994201996279706785739 28754991302994419560178609)
              ·
                refine ⟨21566243477245814670133957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28754991302994419560178609 21566243477245814670133957)
                ·
                  refine ⟨4043670651983590250650117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21566243477245814670133957 4043670651983590250650117)
                  ·
                    refine ⟨758188247246923171996897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4043670651983590250650117 758188247246923171996897)
                    ·
                      rfl

theorem cell23_4429699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 4, 4].length) (baseStart_4429699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4429699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4429699 prefixEnd_4429699 := by exact prefixLift 4429699
  have htrace : WordTrace (prefixWord ++ tailWord_4429699) baseStart_4429699 baseEnd_4429699 := by
    simpa [prefixWord, tailWord_4429699, baseEnd_4429699] using wordTrace_append hprefix tailTrace_4429699
  have hstable : (prefixWord ++ tailWord_4429699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4429699).length < 2 ^ (prefixWord ++ tailWord_4429699).sum := by decide
  have hdescent : baseEnd_4429699 < baseStart_4429699 := by decide
  rcases family_descends (prefixWord ++ tailWord_4429699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4429710 : List Nat := [4, 1, 1, 5, 1, 1, 1, 2, 2, 3, 2]
def baseStart_4429710 : Nat := 118140960795 + 4429710 * 2 ^ 59
def prefixEnd_4429710 : Nat := 4983230072969 + 3 ^ 40 * 4429710 * 2
def baseEnd_4429710 : Nat := 2274570390027968972953141

theorem tailTrace_4429710 : CollatzResearch.WordTrace tailWord_4429710 prefixEnd_4429710 2274570390027968972953141 := by
  unfold tailWord_4429710
  simp only [CollatzResearch.WordTrace]
  refine ⟨20195599597740584885292823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107709864521283119388228389 20195599597740584885292823)
  ·
    refine ⟨30293399396610877327939235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20195599597740584885292823 30293399396610877327939235)
    ·
      refine ⟨45440099094916315991908853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30293399396610877327939235 45440099094916315991908853)
      ·
        refine ⟨4260009290148404624241455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45440099094916315991908853 4260009290148404624241455)
        ·
          refine ⟨6390013935222606936362183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4260009290148404624241455 6390013935222606936362183)
          ·
            refine ⟨9585020902833910404543275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6390013935222606936362183 9585020902833910404543275)
            ·
              refine ⟨14377531354250865606814913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9585020902833910404543275 14377531354250865606814913)
              ·
                refine ⟨10783148515688149205111185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14377531354250865606814913 10783148515688149205111185)
                ·
                  refine ⟨8087361386766111903833389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10783148515688149205111185 8087361386766111903833389)
                  ·
                    refine ⟨3032760520037291963937521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8087361386766111903833389 3032760520037291963937521)
                    ·
                      refine ⟨2274570390027968972953141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3032760520037291963937521 2274570390027968972953141)
                      ·
                        rfl

theorem cell23_4429710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_4429710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4429710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4429710 prefixEnd_4429710 := by exact prefixLift 4429710
  have htrace : WordTrace (prefixWord ++ tailWord_4429710) baseStart_4429710 baseEnd_4429710 := by
    simpa [prefixWord, tailWord_4429710, baseEnd_4429710] using wordTrace_append hprefix tailTrace_4429710
  have hstable : (prefixWord ++ tailWord_4429710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4429710).length < 2 ^ (prefixWord ++ tailWord_4429710).sum := by decide
  have hdescent : baseEnd_4429710 < baseStart_4429710 := by decide
  rcases family_descends (prefixWord ++ tailWord_4429710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4429716 : List Nat := [2, 4, 2, 1, 1, 2, 2, 1, 4, 4]
def baseStart_4429716 : Nat := 118140960795 + 4429716 * 2 ^ 59
def prefixEnd_4429716 : Nat := 4983230072969 + 3 ^ 40 * 4429716 * 2
def baseEnd_4429716 : Nat := 758191156970631983159371

theorem tailTrace_4429716 : CollatzResearch.WordTrace tailWord_4429716 prefixEnd_4429716 758191156970631983159371 := by
  unfold tailWord_4429716
  simp only [CollatzResearch.WordTrace]
  refine ⟨80782507809951471053530501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107710010413268628071374001 80782507809951471053530501)
  ·
    refine ⟨15146720214365900822536969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80782507809951471053530501 15146720214365900822536969)
    ·
      refine ⟨11360040160774425616902727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15146720214365900822536969 11360040160774425616902727)
      ·
        refine ⟨17040060241161638425354091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11360040160774425616902727 17040060241161638425354091)
        ·
          refine ⟨25560090361742457638031137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17040060241161638425354091 25560090361742457638031137)
          ·
            refine ⟨19170067771306843228523353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25560090361742457638031137 19170067771306843228523353)
            ·
              refine ⟨14377550828480132421392515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19170067771306843228523353 14377550828480132421392515)
              ·
                refine ⟨21566326242720198632088773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14377550828480132421392515 21566326242720198632088773)
                ·
                  refine ⟨4043686170510037243516645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21566326242720198632088773 4043686170510037243516645)
                  ·
                    refine ⟨758191156970631983159371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4043686170510037243516645 758191156970631983159371)
                    ·
                      rfl

theorem cell23_4429716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_4429716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4429716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4429716 prefixEnd_4429716 := by exact prefixLift 4429716
  have htrace : WordTrace (prefixWord ++ tailWord_4429716) baseStart_4429716 baseEnd_4429716 := by
    simpa [prefixWord, tailWord_4429716, baseEnd_4429716] using wordTrace_append hprefix tailTrace_4429716
  have hstable : (prefixWord ++ tailWord_4429716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4429716).length < 2 ^ (prefixWord ++ tailWord_4429716).sum := by decide
  have hdescent : baseEnd_4429716 < baseStart_4429716 := by decide
  rcases family_descends (prefixWord ++ tailWord_4429716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4429836 : List Nat := [2, 2, 1, 2, 3, 1, 1, 6, 5]
def baseStart_4429836 : Nat := 118140960795 + 4429836 * 2 ^ 59
def prefixEnd_4429836 : Nat := 4983230072969 + 3 ^ 40 * 4429836 * 2
def baseEnd_4429836 : Nat := 252737232065603942219729

theorem tailTrace_4429836 : CollatzResearch.WordTrace tailWord_4429836 prefixEnd_4429836 252737232065603942219729 := by
  unfold tailWord_4429836
  simp only [CollatzResearch.WordTrace]
  refine ⟨80784696189734101300714681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107712928252978801734286241 80784696189734101300714681)
  ·
    refine ⟨60588522142300575975536011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80784696189734101300714681 60588522142300575975536011)
    ·
      refine ⟨90882783213450863963304017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60588522142300575975536011 90882783213450863963304017)
      ·
        refine ⟨68162087410088147972478013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90882783213450863963304017 68162087410088147972478013)
        ·
          refine ⟨25560782778783055489679255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68162087410088147972478013 25560782778783055489679255)
          ·
            refine ⟨38341174168174583234518883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25560782778783055489679255 38341174168174583234518883)
            ·
              refine ⟨57511761252261874851778325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38341174168174583234518883 57511761252261874851778325)
              ·
                refine ⟨2695863808699775383677109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 57511761252261874851778325 2695863808699775383677109)
                ·
                  refine ⟨252737232065603942219729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2695863808699775383677109 252737232065603942219729)
                  ·
                    rfl

theorem cell23_4429836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 6, 5].length) (baseStart_4429836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4429836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4429836 prefixEnd_4429836 := by exact prefixLift 4429836
  have htrace : WordTrace (prefixWord ++ tailWord_4429836) baseStart_4429836 baseEnd_4429836 := by
    simpa [prefixWord, tailWord_4429836, baseEnd_4429836] using wordTrace_append hprefix tailTrace_4429836
  have hstable : (prefixWord ++ tailWord_4429836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4429836).length < 2 ^ (prefixWord ++ tailWord_4429836).sum := by decide
  have hdescent : baseEnd_4429836 < baseStart_4429836 := by decide
  rcases family_descends (prefixWord ++ tailWord_4429836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4429847 : List Nat := [1, 1, 3, 5, 3, 1, 1, 1, 1, 4, 2]
def baseStart_4429847 : Nat := 118140960795 + 4429847 * 2 ^ 59
def prefixEnd_4429847 : Nat := 4983230072969 + 3 ^ 40 * 4429847 * 2
def baseEnd_4429847 : Nat := 2274640736877634936940011

theorem tailTrace_4429847 : CollatzResearch.WordTrace tailWord_4429847 prefixEnd_4429847 2274640736877634936940011 := by
  unfold tailWord_4429847
  simp only [CollatzResearch.WordTrace]
  refine ⟨161569793582428351480079795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107713195721618900986719863 161569793582428351480079795)
  ·
    refine ⟨242354690373642527220119693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161569793582428351480079795 242354690373642527220119693)
    ·
      refine ⟨90883008890115947707544885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 242354690373642527220119693 90883008890115947707544885)
      ·
        refine ⟨8520282083448370097582333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 90883008890115947707544885 8520282083448370097582333)
        ·
          refine ⟨3195105781293138786593375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8520282083448370097582333 3195105781293138786593375)
          ·
            refine ⟨4792658671939708179890063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3195105781293138786593375 4792658671939708179890063)
            ·
              refine ⟨7188988007909562269835095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4792658671939708179890063 7188988007909562269835095)
              ·
                refine ⟨10783482011864343404752643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7188988007909562269835095 10783482011864343404752643)
                ·
                  refine ⟨16175223017796515107128965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10783482011864343404752643 16175223017796515107128965)
                  ·
                    refine ⟨3032854315836846582586681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16175223017796515107128965 3032854315836846582586681)
                    ·
                      refine ⟨2274640736877634936940011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3032854315836846582586681 2274640736877634936940011)
                      ·
                        rfl

theorem cell23_4429847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_4429847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4429847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4429847 prefixEnd_4429847 := by exact prefixLift 4429847
  have htrace : WordTrace (prefixWord ++ tailWord_4429847) baseStart_4429847 baseEnd_4429847 := by
    simpa [prefixWord, tailWord_4429847, baseEnd_4429847] using wordTrace_append hprefix tailTrace_4429847
  have hstable : (prefixWord ++ tailWord_4429847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4429847).length < 2 ^ (prefixWord ++ tailWord_4429847).sum := by decide
  have hdescent : baseEnd_4429847 < baseStart_4429847 := by decide
  rcases family_descends (prefixWord ++ tailWord_4429847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4429866 : List Nat := [3, 1, 4, 1, 2, 1, 2, 1, 1, 7]
def baseStart_4429866 : Nat := 118140960795 + 4429866 * 2 ^ 59
def prefixEnd_4429866 : Nat := 4983230072969 + 3 ^ 40 * 4429866 * 2
def baseEnd_4429866 : Nat := 758216831003356787534141

theorem tailTrace_4429866 : CollatzResearch.WordTrace tailWord_4429866 prefixEnd_4429866 758216831003356787534141 := by
  unfold tailWord_4429866
  simp only [CollatzResearch.WordTrace]
  refine ⟨40392621642339879431255363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107713657712906345150014301 40392621642339879431255363)
  ·
    refine ⟨60588932463509819146883045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40392621642339879431255363 60588932463509819146883045)
    ·
      refine ⟨11360424836908091090040571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60588932463509819146883045 11360424836908091090040571)
      ·
        refine ⟨17040637255362136635060857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11360424836908091090040571 17040637255362136635060857)
        ·
          refine ⟨12780477941521602476295643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17040637255362136635060857 12780477941521602476295643)
          ·
            refine ⟨19170716912282403714443465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12780477941521602476295643 19170716912282403714443465)
            ·
              refine ⟨14378037684211802785832599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19170716912282403714443465 14378037684211802785832599)
              ·
                refine ⟨21567056526317704178748899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14378037684211802785832599 21567056526317704178748899)
                ·
                  refine ⟨32350584789476556268123349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21567056526317704178748899 32350584789476556268123349)
                  ·
                    refine ⟨758216831003356787534141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32350584789476556268123349 758216831003356787534141)
                    ·
                      rfl

theorem cell23_4429866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_4429866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4429866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4429866 prefixEnd_4429866 := by exact prefixLift 4429866
  have htrace : WordTrace (prefixWord ++ tailWord_4429866) baseStart_4429866 baseEnd_4429866 := by
    simpa [prefixWord, tailWord_4429866, baseEnd_4429866] using wordTrace_append hprefix tailTrace_4429866
  have hstable : (prefixWord ++ tailWord_4429866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4429866).length < 2 ^ (prefixWord ++ tailWord_4429866).sum := by decide
  have hdescent : baseEnd_4429866 < baseStart_4429866 := by decide
  rcases family_descends (prefixWord ++ tailWord_4429866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4429870 : List Nat := [4, 1, 3, 1, 1, 4, 1, 3, 5]
def baseStart_4429870 : Nat := 118140960795 + 4429870 * 2 ^ 59
def prefixEnd_4429870 : Nat := 4983230072969 + 3 ^ 40 * 4429870 * 2
def baseEnd_4429870 : Nat := 252739171881409816328045

theorem tailTrace_4429870 : CollatzResearch.WordTrace tailWord_4429870 prefixEnd_4429870 252739171881409816328045 := by
  unfold tailWord_4429870
  simp only [CollatzResearch.WordTrace]
  refine ⟨20196329057668128301020883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107713754974230017605444709 20196329057668128301020883)
  ·
    refine ⟨30294493586502192451531325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20196329057668128301020883 30294493586502192451531325)
    ·
      refine ⟨11360435094938322169324247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30294493586502192451531325 11360435094938322169324247)
      ·
        refine ⟨17040652642407483253986371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11360435094938322169324247 17040652642407483253986371)
        ·
          refine ⟨25560978963611224880979557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17040652642407483253986371 25560978963611224880979557)
          ·
            refine ⟨4792683555677104665183667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25560978963611224880979557 4792683555677104665183667)
            ·
              refine ⟨7189025333515656997775501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4792683555677104665183667 7189025333515656997775501)
              ·
                refine ⟨2695884500068371374165813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7189025333515656997775501 2695884500068371374165813)
                ·
                  refine ⟨252739171881409816328045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2695884500068371374165813 252739171881409816328045)
                  ·
                    rfl

theorem cell23_4429870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 3, 5].length) (baseStart_4429870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4429870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4429870 prefixEnd_4429870 := by exact prefixLift 4429870
  have htrace : WordTrace (prefixWord ++ tailWord_4429870) baseStart_4429870 baseEnd_4429870 := by
    simpa [prefixWord, tailWord_4429870, baseEnd_4429870] using wordTrace_append hprefix tailTrace_4429870
  have hstable : (prefixWord ++ tailWord_4429870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4429870).length < 2 ^ (prefixWord ++ tailWord_4429870).sum := by decide
  have hdescent : baseEnd_4429870 < baseStart_4429870 := by decide
  rcases family_descends (prefixWord ++ tailWord_4429870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4429896 : List Nat := [2, 1, 3, 1, 1, 1, 2, 5, 3, 4]
def baseStart_4429896 : Nat := 118140960795 + 4429896 * 2 ^ 59
def prefixEnd_4429896 : Nat := 4983230072969 + 3 ^ 40 * 4429896 * 2
def baseEnd_4429896 : Nat := 758221965809901748409095

theorem tailTrace_4429896 : CollatzResearch.WordTrace tailWord_4429896 prefixEnd_4429896 758221965809901748409095 := by
  unfold tailWord_4429896
  simp only [CollatzResearch.WordTrace]
  refine ⟨80785790379625416424306771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107714387172833888565742361 80785790379625416424306771)
  ·
    refine ⟨121178685569438124636460157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80785790379625416424306771 121178685569438124636460157)
    ·
      refine ⟨45442007088539296738672559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121178685569438124636460157 45442007088539296738672559)
      ·
        refine ⟨68163010632808945108008839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45442007088539296738672559 68163010632808945108008839)
        ·
          refine ⟨102244515949213417662013259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68163010632808945108008839 102244515949213417662013259)
          ·
            refine ⟨153366773923820126493019889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102244515949213417662013259 153366773923820126493019889)
            ·
              refine ⟨115025080442865094869764917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 153366773923820126493019889 115025080442865094869764917)
              ·
                refine ⟨10783601291518602644040461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 115025080442865094869764917 10783601291518602644040461)
                ·
                  refine ⟨4043850484319475991515173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10783601291518602644040461 4043850484319475991515173)
                  ·
                    refine ⟨758221965809901748409095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4043850484319475991515173 758221965809901748409095)
                    ·
                      rfl

theorem cell23_4429896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5, 3, 4].length) (baseStart_4429896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4429896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4429896 prefixEnd_4429896 := by exact prefixLift 4429896
  have htrace : WordTrace (prefixWord ++ tailWord_4429896) baseStart_4429896 baseEnd_4429896 := by
    simpa [prefixWord, tailWord_4429896, baseEnd_4429896] using wordTrace_append hprefix tailTrace_4429896
  have hstable : (prefixWord ++ tailWord_4429896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4429896).length < 2 ^ (prefixWord ++ tailWord_4429896).sum := by decide
  have hdescent : baseEnd_4429896 < baseStart_4429896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4429896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4429956 : List Nat := [2, 3, 2, 1, 2, 1, 1, 1, 5, 5]
def baseStart_4429956 : Nat := 118140960795 + 4429956 * 2 ^ 59
def prefixEnd_4429956 : Nat := 4983230072969 + 3 ^ 40 * 4429956 * 2
def baseEnd_4429956 : Nat := 758232235422991670159003

theorem tailTrace_4429956 : CollatzResearch.WordTrace tailWord_4429956 prefixEnd_4429956 758232235422991670159003 := by
  unfold tailWord_4429956
  simp only [CollatzResearch.WordTrace]
  refine ⟨80786884569516731547898861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107715846092688975397198481 80786884569516731547898861)
  ·
    refine ⟨30295081713568774330462073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80786884569516731547898861 30295081713568774330462073)
    ·
      refine ⟨22721311285176580747846555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30295081713568774330462073 22721311285176580747846555)
      ·
        refine ⟨34081966927764871121769833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22721311285176580747846555 34081966927764871121769833)
        ·
          refine ⟨25561475195823653341327375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34081966927764871121769833 25561475195823653341327375)
          ·
            refine ⟨38342212793735480011991063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25561475195823653341327375 38342212793735480011991063)
            ·
              refine ⟨57513319190603220017986595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38342212793735480011991063 57513319190603220017986595)
              ·
                refine ⟨86269978785904830026979893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57513319190603220017986595 86269978785904830026979893)
                ·
                  refine ⟨8087810511178577815029365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 86269978785904830026979893 8087810511178577815029365)
                  ·
                    refine ⟨758232235422991670159003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8087810511178577815029365 758232235422991670159003)
                    ·
                      rfl

theorem cell23_4429956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_4429956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4429956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4429956 prefixEnd_4429956 := by exact prefixLift 4429956
  have htrace : WordTrace (prefixWord ++ tailWord_4429956) baseStart_4429956 baseEnd_4429956 := by
    simpa [prefixWord, tailWord_4429956, baseEnd_4429956] using wordTrace_append hprefix tailTrace_4429956
  have hstable : (prefixWord ++ tailWord_4429956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4429956).length < 2 ^ (prefixWord ++ tailWord_4429956).sum := by decide
  have hdescent : baseEnd_4429956 < baseStart_4429956 := by decide
  rcases family_descends (prefixWord ++ tailWord_4429956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4429970 : List Nat := [3, 2, 3, 1, 1, 1, 3, 2, 3, 1, 3]
def baseStart_4429970 : Nat := 118140960795 + 4429970 * 2 ^ 59
def prefixEnd_4429970 : Nat := 4983230072969 + 3 ^ 40 * 4429970 * 2
def baseEnd_4429970 : Nat := 2274703894998137955701945

theorem tailTrace_4429970 : CollatzResearch.WordTrace tailWord_4429970 prefixEnd_4429970 2274703894998137955701945 := by
  unfold tailWord_4429970
  simp only [CollatzResearch.WordTrace]
  refine ⟨40393569940245685871701841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107716186507321828991204909 40393569940245685871701841)
  ·
    refine ⟨30295177455184264403776381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40393569940245685871701841 30295177455184264403776381)
    ·
      refine ⟨11360691545694099151416143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30295177455184264403776381 11360691545694099151416143)
      ·
        refine ⟨17041037318541148727124215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11360691545694099151416143 17041037318541148727124215)
        ·
          refine ⟨25561555977811723090686323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17041037318541148727124215 25561555977811723090686323)
          ·
            refine ⟨38342333966717584636029485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25561555977811723090686323 38342333966717584636029485)
            ·
              refine ⟨14378375237519094238511057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38342333966717584636029485 14378375237519094238511057)
              ·
                refine ⟨10783781428139320678883293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14378375237519094238511057 10783781428139320678883293)
                ·
                  refine ⟨4043918035552245254581235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10783781428139320678883293 4043918035552245254581235)
                  ·
                    refine ⟨6065877053328367881871853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4043918035552245254581235 6065877053328367881871853)
                    ·
                      refine ⟨2274703894998137955701945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6065877053328367881871853 2274703894998137955701945)
                      ·
                        rfl

theorem cell23_4429970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_4429970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4429970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4429970 prefixEnd_4429970 := by exact prefixLift 4429970
  have htrace : WordTrace (prefixWord ++ tailWord_4429970) baseStart_4429970 baseEnd_4429970 := by
    simpa [prefixWord, tailWord_4429970, baseEnd_4429970] using wordTrace_append hprefix tailTrace_4429970
  have hstable : (prefixWord ++ tailWord_4429970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4429970).length < 2 ^ (prefixWord ++ tailWord_4429970).sum := by decide
  have hdescent : baseEnd_4429970 < baseStart_4429970 := by decide
  rcases family_descends (prefixWord ++ tailWord_4429970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4430010 : List Nat := [3, 1, 1, 1, 2, 2, 3, 3, 3, 2, 2]
def baseStart_4430010 : Nat := 118140960795 + 4430010 * 2 ^ 59
def prefixEnd_4430010 : Nat := 4983230072969 + 3 ^ 40 * 4430010 * 2
def baseEnd_4430010 : Nat := 2274724434224317799201761

theorem tailTrace_4430010 : CollatzResearch.WordTrace tailWord_4430010 prefixEnd_4430010 2274724434224317799201761 := by
  unfold tailWord_4430010
  simp only [CollatzResearch.WordTrace]
  refine ⟨40393934670209457579565871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107717159120558553545508989 40393934670209457579565871)
  ·
    refine ⟨60590902005314186369348807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40393934670209457579565871 60590902005314186369348807)
    ·
      refine ⟨90886353007971279554023211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60590902005314186369348807 90886353007971279554023211)
      ·
        refine ⟨136329529511956919331034817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90886353007971279554023211 136329529511956919331034817)
        ·
          refine ⟨102247147133967689498276113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136329529511956919331034817 102247147133967689498276113)
          ·
            refine ⟨76685360350475767123707085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102247147133967689498276113 76685360350475767123707085)
            ·
              refine ⟨28757010131428412671390157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76685360350475767123707085 28757010131428412671390157)
              ·
                refine ⟨10783878799285654751771309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28757010131428412671390157 10783878799285654751771309)
                ·
                  refine ⟨4043954549732120531914241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10783878799285654751771309 4043954549732120531914241)
                  ·
                    refine ⟨3032965912299090398935681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4043954549732120531914241 3032965912299090398935681)
                    ·
                      refine ⟨2274724434224317799201761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3032965912299090398935681 2274724434224317799201761)
                      ·
                        rfl

theorem cell23_4430010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3, 3, 2, 2].length) (baseStart_4430010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4430010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4430010 prefixEnd_4430010 := by exact prefixLift 4430010
  have htrace : WordTrace (prefixWord ++ tailWord_4430010) baseStart_4430010 baseEnd_4430010 := by
    simpa [prefixWord, tailWord_4430010, baseEnd_4430010] using wordTrace_append hprefix tailTrace_4430010
  have hstable : (prefixWord ++ tailWord_4430010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4430010).length < 2 ^ (prefixWord ++ tailWord_4430010).sum := by decide
  have hdescent : baseEnd_4430010 < baseStart_4430010 := by decide
  rcases family_descends (prefixWord ++ tailWord_4430010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4430020 : List Nat := [2, 3, 3, 1, 2, 3, 1, 1, 1, 6]
def baseStart_4430020 : Nat := 118140960795 + 4430020 * 2 ^ 59
def prefixEnd_4430020 : Nat := 4983230072969 + 3 ^ 40 * 4430020 * 2
def baseEnd_4430020 : Nat := 758243189676954253358905

theorem tailTrace_4430020 : CollatzResearch.WordTrace tailWord_4430020 prefixEnd_4430020 758243189676954253358905 := by
  unfold tailWord_4430020
  simp only [CollatzResearch.WordTrace]
  refine ⟨80788051705400801013063757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107717402273867734684085009 80788051705400801013063757)
  ·
    refine ⟨30295519389525300379898909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80788051705400801013063757 30295519389525300379898909)
    ·
      refine ⟨11360819771071987642462091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30295519389525300379898909 11360819771071987642462091)
      ·
        refine ⟨17041229656607981463693137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11360819771071987642462091 17041229656607981463693137)
        ·
          refine ⟨12780922242455986097769853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17041229656607981463693137 12780922242455986097769853)
          ·
            refine ⟨4792845840920994786663695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12780922242455986097769853 4792845840920994786663695)
            ·
              refine ⟨7189268761381492179995543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4792845840920994786663695 7189268761381492179995543)
              ·
                refine ⟨10783903142072238269993315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7189268761381492179995543 10783903142072238269993315)
                ·
                  refine ⟨16175854713108357404989973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10783903142072238269993315 16175854713108357404989973)
                  ·
                    refine ⟨758243189676954253358905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16175854713108357404989973 758243189676954253358905)
                    ·
                      rfl

theorem cell23_4430020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_4430020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4430020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4430020 prefixEnd_4430020 := by exact prefixLift 4430020
  have htrace : WordTrace (prefixWord ++ tailWord_4430020) baseStart_4430020 baseEnd_4430020 := by
    simpa [prefixWord, tailWord_4430020, baseEnd_4430020] using wordTrace_append hprefix tailTrace_4430020
  have hstable : (prefixWord ++ tailWord_4430020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4430020).length < 2 ^ (prefixWord ++ tailWord_4430020).sum := by decide
  have hdescent : baseEnd_4430020 < baseStart_4430020 := by decide
  rcases family_descends (prefixWord ++ tailWord_4430020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4430030 : List Nat := [4, 1, 1, 1, 4, 1, 1, 4, 1, 2, 3]
def baseStart_4430030 : Nat := 118140960795 + 4430030 * 2 ^ 59
def prefixEnd_4430030 : Nat := 4983230072969 + 3 ^ 40 * 4430030 * 2
def baseEnd_4430030 : Nat := 2274734703837407720951669

theorem tailTrace_4430030 : CollatzResearch.WordTrace tailWord_4430030 prefixEnd_4430030 2274734703837407720951669 := by
  unfold tailWord_4430030
  simp only [CollatzResearch.WordTrace]
  refine ⟨20197058517595671716748943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107717645427176915822661029 20197058517595671716748943)
  ·
    refine ⟨30295587776393507575123415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20197058517595671716748943 30295587776393507575123415)
    ·
      refine ⟨45443381664590261362685123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30295587776393507575123415 45443381664590261362685123)
      ·
        refine ⟨68165072496885392044027685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45443381664590261362685123 68165072496885392044027685)
        ·
          refine ⟨12780951093166011008255191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68165072496885392044027685 12780951093166011008255191)
          ·
            refine ⟨19171426639749016512382787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12780951093166011008255191 19171426639749016512382787)
            ·
              refine ⟨28757139959623524768574181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19171426639749016512382787 28757139959623524768574181)
              ·
                refine ⟨5391963742429410894107659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28757139959623524768574181 5391963742429410894107659)
                ·
                  refine ⟨8087945613644116341161489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5391963742429410894107659 8087945613644116341161489)
                  ·
                    refine ⟨6065959210233087255871117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8087945613644116341161489 6065959210233087255871117)
                    ·
                      refine ⟨2274734703837407720951669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6065959210233087255871117 2274734703837407720951669)
                      ·
                        rfl

theorem cell23_4430030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 4, 1, 2, 3].length) (baseStart_4430030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4430030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4430030 prefixEnd_4430030 := by exact prefixLift 4430030
  have htrace : WordTrace (prefixWord ++ tailWord_4430030) baseStart_4430030 baseEnd_4430030 := by
    simpa [prefixWord, tailWord_4430030, baseEnd_4430030] using wordTrace_append hprefix tailTrace_4430030
  have hstable : (prefixWord ++ tailWord_4430030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4430030).length < 2 ^ (prefixWord ++ tailWord_4430030).sum := by decide
  have hdescent : baseEnd_4430030 < baseStart_4430030 := by decide
  rcases family_descends (prefixWord ++ tailWord_4430030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4430043 : List Nat := [1, 1, 1, 1, 1, 1, 1, 8, 4, 1, 3]
def baseStart_4430043 : Nat := 118140960795 + 4430043 * 2 ^ 59
def prefixEnd_4430043 : Nat := 4983230072969 + 3 ^ 40 * 4430043 * 2
def baseEnd_4430043 : Nat := 2274741379085916170089109

theorem tailTrace_4430043 : CollatzResearch.WordTrace tailWord_4430043 prefixEnd_4430043 2274741379085916170089109 := by
  unfold tailWord_4430043
  simp only [CollatzResearch.WordTrace]
  refine ⟨161576942289718276954214783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107717961526478851302809855 161576942289718276954214783)
  ·
    refine ⟨242365413434577415431322175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161576942289718276954214783 242365413434577415431322175)
    ·
      refine ⟨363548120151866123146983263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242365413434577415431322175 363548120151866123146983263)
      ·
        refine ⟨545322180227799184720474895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 363548120151866123146983263 545322180227799184720474895)
        ·
          refine ⟨817983270341698777080712343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 545322180227799184720474895 817983270341698777080712343)
          ·
            refine ⟨1226974905512548165621068515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 817983270341698777080712343 1226974905512548165621068515)
            ·
              refine ⟨1840462358268822248431602773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1226974905512548165621068515 1840462358268822248431602773)
              ·
                refine ⟨21567918260962760723807845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1840462358268822248431602773 21567918260962760723807845)
                ·
                  refine ⟨4043984673930517635713971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21567918260962760723807845 4043984673930517635713971)
                  ·
                    refine ⟨6065977010895776453570957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4043984673930517635713971 6065977010895776453570957)
                    ·
                      refine ⟨2274741379085916170089109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6065977010895776453570957 2274741379085916170089109)
                      ·
                        rfl

theorem cell23_4430043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 4, 1, 3].length) (baseStart_4430043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4430043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4430043 prefixEnd_4430043 := by exact prefixLift 4430043
  have htrace : WordTrace (prefixWord ++ tailWord_4430043) baseStart_4430043 baseEnd_4430043 := by
    simpa [prefixWord, tailWord_4430043, baseEnd_4430043] using wordTrace_append hprefix tailTrace_4430043
  have hstable : (prefixWord ++ tailWord_4430043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4430043).length < 2 ^ (prefixWord ++ tailWord_4430043).sum := by decide
  have hdescent : baseEnd_4430043 < baseStart_4430043 := by decide
  rcases family_descends (prefixWord ++ tailWord_4430043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4430060 : List Nat := [2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 3]
def baseStart_4430060 : Nat := 118140960795 + 4430060 * 2 ^ 59
def prefixEnd_4430060 : Nat := 4983230072969 + 3 ^ 40 * 4430060 * 2
def baseEnd_4430060 : Nat := 2274750108257042603576531

theorem tailTrace_4430060 : CollatzResearch.WordTrace tailWord_4430060 prefixEnd_4430060 2274750108257042603576531 := by
  unfold tailWord_4430060
  simp only [CollatzResearch.WordTrace]
  refine ⟨80788781165328344428791817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107718374887104459238389089 80788781165328344428791817)
  ·
    refine ⟨60591585873996258321593863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80788781165328344428791817 60591585873996258321593863)
    ·
      refine ⟨90887378810994387482390795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60591585873996258321593863 90887378810994387482390795)
      ·
        refine ⟨136331068216491581223586193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90887378810994387482390795 136331068216491581223586193)
        ·
          refine ⟨102248301162368685917689645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136331068216491581223586193 102248301162368685917689645)
          ·
            refine ⟨38343112935888257219133617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102248301162368685917689645 38343112935888257219133617)
            ·
              refine ⟨28757334701916192914350213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38343112935888257219133617 28757334701916192914350213)
              ·
                refine ⟨5392000256609286171440665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28757334701916192914350213 5392000256609286171440665)
                ·
                  refine ⟨4044000192456964628580499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5392000256609286171440665 4044000192456964628580499)
                  ·
                    refine ⟨6066000288685446942870749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4044000192456964628580499 6066000288685446942870749)
                    ·
                      refine ⟨2274750108257042603576531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6066000288685446942870749 2274750108257042603576531)
                      ·
                        rfl

theorem cell23_4430060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 3].length) (baseStart_4430060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4430060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4430060 prefixEnd_4430060 := by exact prefixLift 4430060
  have htrace : WordTrace (prefixWord ++ tailWord_4430060) baseStart_4430060 baseEnd_4430060 := by
    simpa [prefixWord, tailWord_4430060, baseEnd_4430060] using wordTrace_append hprefix tailTrace_4430060
  have hstable : (prefixWord ++ tailWord_4430060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4430060).length < 2 ^ (prefixWord ++ tailWord_4430060).sum := by decide
  have hdescent : baseEnd_4430060 < baseStart_4430060 := by decide
  rcases family_descends (prefixWord ++ tailWord_4430060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4430061 : List Nat := [1, 5, 1, 2, 4, 1, 1, 1, 3, 2, 2]
def baseStart_4430061 : Nat := 118140960795 + 4430061 * 2 ^ 59
def prefixEnd_4430061 : Nat := 4983230072969 + 3 ^ 40 * 4430061 * 2
def baseEnd_4430061 : Nat := 2274750621737697099664027

theorem tailTrace_4430061 : CollatzResearch.WordTrace tailWord_4430061 prefixEnd_4430061 2274750621737697099664027 := by
  unfold tailWord_4430061
  simp only [CollatzResearch.WordTrace]
  refine ⟨161577598803653066028370037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107718399202435377352246691 161577598803653066028370037)
  ·
    refine ⟨15147899887842474940159691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 161577598803653066028370037 15147899887842474940159691)
    ·
      refine ⟨22721849831763712410239537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15147899887842474940159691 22721849831763712410239537)
      ·
        refine ⟨17041387373822784307679653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22721849831763712410239537 17041387373822784307679653)
        ·
          refine ⟨3195260132591772057689935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17041387373822784307679653 3195260132591772057689935)
          ·
            refine ⟨4792890198887658086534903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3195260132591772057689935 4792890198887658086534903)
            ·
              refine ⟨7189335298331487129802355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4792890198887658086534903 7189335298331487129802355)
              ·
                refine ⟨10784002947497230694703533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7189335298331487129802355 10784002947497230694703533)
                ·
                  refine ⟨4044001105311461510513825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10784002947497230694703533 4044001105311461510513825)
                  ·
                    refine ⟨3033000828983596132885369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4044001105311461510513825 3033000828983596132885369)
                    ·
                      refine ⟨2274750621737697099664027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3033000828983596132885369 2274750621737697099664027)
                      ·
                        rfl

theorem cell23_4430061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_4430061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4430061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4430061 prefixEnd_4430061 := by exact prefixLift 4430061
  have htrace : WordTrace (prefixWord ++ tailWord_4430061) baseStart_4430061 baseEnd_4430061 := by
    simpa [prefixWord, tailWord_4430061, baseEnd_4430061] using wordTrace_append hprefix tailTrace_4430061
  have hstable : (prefixWord ++ tailWord_4430061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4430061).length < 2 ^ (prefixWord ++ tailWord_4430061).sum := by decide
  have hdescent : baseEnd_4430061 < baseStart_4430061 := by decide
  rcases family_descends (prefixWord ++ tailWord_4430061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4430103 : List Nat := [1, 1, 3, 4, 1, 2, 2, 1, 2, 1, 5]
def baseStart_4430103 : Nat := 118140960795 + 4430103 * 2 ^ 59
def prefixEnd_4430103 : Nat := 4983230072969 + 3 ^ 40 * 4430103 * 2
def baseEnd_4430103 : Nat := 2274772187925185935338833

theorem tailTrace_4430103 : CollatzResearch.WordTrace tailWord_4430103 prefixEnd_4430103 2274772187925185935338833 := by
  unfold tailWord_4430103
  simp only [CollatzResearch.WordTrace]
  refine ⟨161579130669500907201398963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107719420446333938134265975 161579130669500907201398963)
  ·
    refine ⟨242368696004251360802098445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161579130669500907201398963 242368696004251360802098445)
    ·
      refine ⟨90888261001594260300786917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 242368696004251360802098445 90888261001594260300786917)
      ·
        refine ⟨17041548937798923806397547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90888261001594260300786917 17041548937798923806397547)
        ·
          refine ⟨25562323406698385709596321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17041548937798923806397547 25562323406698385709596321)
          ·
            refine ⟨19171742555023789282197241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25562323406698385709596321 19171742555023789282197241)
            ·
              refine ⟨14378806916267841961647931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19171742555023789282197241 14378806916267841961647931)
              ·
                refine ⟨21568210374401762942471897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14378806916267841961647931 21568210374401762942471897)
                ·
                  refine ⟨16176157780801322206853923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21568210374401762942471897 16176157780801322206853923)
                  ·
                    refine ⟨24264236671201983310280885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16176157780801322206853923 24264236671201983310280885)
                    ·
                      refine ⟨2274772187925185935338833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24264236671201983310280885 2274772187925185935338833)
                      ·
                        rfl

theorem cell23_4430103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_4430103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4430103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4430103 prefixEnd_4430103 := by exact prefixLift 4430103
  have htrace : WordTrace (prefixWord ++ tailWord_4430103) baseStart_4430103 baseEnd_4430103 := by
    simpa [prefixWord, tailWord_4430103, baseEnd_4430103] using wordTrace_append hprefix tailTrace_4430103
  have hstable : (prefixWord ++ tailWord_4430103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4430103).length < 2 ^ (prefixWord ++ tailWord_4430103).sum := by decide
  have hdescent : baseEnd_4430103 < baseStart_4430103 := by decide
  rcases family_descends (prefixWord ++ tailWord_4430103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4430130 : List Nat := [3, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4]
def baseStart_4430130 : Nat := 118140960795 + 4430130 * 2 ^ 59
def prefixEnd_4430130 : Nat := 4983230072969 + 3 ^ 40 * 4430130 * 2
def baseEnd_4430130 : Nat := 2274786051902857329701209

theorem tailTrace_4430130 : CollatzResearch.WordTrace tailWord_4430130 prefixEnd_4430130 2274786051902857329701209 := by
  unfold tailWord_4430130
  simp only [CollatzResearch.WordTrace]
  refine ⟨40395028860100772703157961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107720076960268727208421229 40395028860100772703157961)
  ·
    refine ⟨30296271645075579527368471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40395028860100772703157961 30296271645075579527368471)
    ·
      refine ⟨45444407467613369291052707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30296271645075579527368471 45444407467613369291052707)
      ·
        refine ⟨68166611201420053936579061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45444407467613369291052707 68166611201420053936579061)
        ·
          refine ⟨6390619800133130056554287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68166611201420053936579061 6390619800133130056554287)
          ·
            refine ⟨9585929700199695084831431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6390619800133130056554287 9585929700199695084831431)
            ·
              refine ⟨14378894550299542627247147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9585929700199695084831431 14378894550299542627247147)
              ·
                refine ⟨21568341825449313940870721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14378894550299542627247147 21568341825449313940870721)
                ·
                  refine ⟨16176256369086985455653041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21568341825449313940870721 16176256369086985455653041)
                  ·
                    refine ⟨12132192276815239091739781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16176256369086985455653041 12132192276815239091739781)
                    ·
                      refine ⟨2274786051902857329701209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12132192276815239091739781 2274786051902857329701209)
                      ·
                        rfl

theorem cell23_4430130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4].length) (baseStart_4430130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4430130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4430130 prefixEnd_4430130 := by exact prefixLift 4430130
  have htrace : WordTrace (prefixWord ++ tailWord_4430130) baseStart_4430130 baseEnd_4430130 := by
    simpa [prefixWord, tailWord_4430130, baseEnd_4430130] using wordTrace_append hprefix tailTrace_4430130
  have hstable : (prefixWord ++ tailWord_4430130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4430130).length < 2 ^ (prefixWord ++ tailWord_4430130).sum := by decide
  have hdescent : baseEnd_4430130 < baseStart_4430130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4430130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4430247 : List Nat := [1, 1, 6, 1, 1, 2, 4, 1, 6]
def baseStart_4430247 : Nat := 118140960795 + 4430247 * 2 ^ 59
def prefixEnd_4430247 : Nat := 4983230072969 + 3 ^ 40 * 4430247 * 2
def baseEnd_4430247 : Nat := 252760681015492596882019

theorem tailTrace_4430247 : CollatzResearch.WordTrace tailWord_4430247 prefixEnd_4430247 252760681015492596882019 := by
  unfold tailWord_4430247
  simp only [CollatzResearch.WordTrace]
  refine ⟨161584382780979219794640995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107722921853986146529760663 161584382780979219794640995)
  ·
    refine ⟨242376574171468829691961493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161584382780979219794640995 242376574171468829691961493)
    ·
      refine ⟨11361401914287601391810695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 242376574171468829691961493 11361401914287601391810695)
      ·
        refine ⟨17042102871431402087716043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11361401914287601391810695 17042102871431402087716043)
        ·
          refine ⟨25563154307147103131574065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17042102871431402087716043 25563154307147103131574065)
          ·
            refine ⟨19172365730360327348680549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25563154307147103131574065 19172365730360327348680549)
            ·
              refine ⟨3594818574442561377877603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19172365730360327348680549 3594818574442561377877603)
              ·
                refine ⟨5392227861663842066816405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3594818574442561377877603 5392227861663842066816405)
                ·
                  refine ⟨252760681015492596882019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5392227861663842066816405 252760681015492596882019)
                  ·
                    rfl

theorem cell23_4430247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4, 1, 6].length) (baseStart_4430247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4430247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4430247 prefixEnd_4430247 := by exact prefixLift 4430247
  have htrace : WordTrace (prefixWord ++ tailWord_4430247) baseStart_4430247 baseEnd_4430247 := by
    simpa [prefixWord, tailWord_4430247, baseEnd_4430247] using wordTrace_append hprefix tailTrace_4430247
  have hstable : (prefixWord ++ tailWord_4430247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4430247).length < 2 ^ (prefixWord ++ tailWord_4430247).sum := by decide
  have hdescent : baseEnd_4430247 < baseStart_4430247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4430247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4430307 : List Nat := [1, 1, 1, 6, 3, 1, 2, 1, 1, 6]
def baseStart_4430307 : Nat := 118140960795 + 4430307 * 2 ^ 59
def prefixEnd_4430307 : Nat := 4983230072969 + 3 ^ 40 * 4430307 * 2
def baseEnd_4430307 : Nat := 758292312659567712395965

theorem tailTrace_4430307 : CollatzResearch.WordTrace tailWord_4430307 prefixEnd_4430307 758292312659567712395965 := by
  unfold tailWord_4430307
  simp only [CollatzResearch.WordTrace]
  refine ⟨161586571160761850041825175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107724380773841233361216783 161586571160761850041825175)
  ·
    refine ⟨242379856741142775062737763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161586571160761850041825175 242379856741142775062737763)
    ·
      refine ⟨363569785111714162594106645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242379856741142775062737763 363569785111714162594106645)
      ·
        refine ⟨17042333677111601371598749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 363569785111714162594106645 17042333677111601371598749)
        ·
          refine ⟨6390875128916850514349531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17042333677111601371598749 6390875128916850514349531)
          ·
            refine ⟨9586312693375275771524297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6390875128916850514349531 9586312693375275771524297)
            ·
              refine ⟨7189734520031456828643223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9586312693375275771524297 7189734520031456828643223)
              ·
                refine ⟨10784601780047185242964835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7189734520031456828643223 10784601780047185242964835)
                ·
                  refine ⟨16176902670070777864447253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10784601780047185242964835 16176902670070777864447253)
                  ·
                    refine ⟨758292312659567712395965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16176902670070777864447253 758292312659567712395965)
                    ·
                      rfl

theorem cell23_4430307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 1, 1, 6].length) (baseStart_4430307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4430307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4430307 prefixEnd_4430307 := by exact prefixLift 4430307
  have htrace : WordTrace (prefixWord ++ tailWord_4430307) baseStart_4430307 baseEnd_4430307 := by
    simpa [prefixWord, tailWord_4430307, baseEnd_4430307] using wordTrace_append hprefix tailTrace_4430307
  have hstable : (prefixWord ++ tailWord_4430307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4430307).length < 2 ^ (prefixWord ++ tailWord_4430307).sum := by decide
  have hdescent : baseEnd_4430307 < baseStart_4430307 := by decide
  rcases family_descends (prefixWord ++ tailWord_4430307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4430314 : List Nat := [3, 1, 3, 1, 3, 1, 1, 1, 5, 2, 2]
def baseStart_4430314 : Nat := 118140960795 + 4430314 * 2 ^ 59
def prefixEnd_4430314 : Nat := 4983230072969 + 3 ^ 40 * 4430314 * 2
def baseEnd_4430314 : Nat := 2274880532343284609800363

theorem tailTrace_4430314 : CollatzResearch.WordTrace tailWord_4430314 prefixEnd_4430314 2274880532343284609800363 := by
  unfold tailWord_4430314
  simp only [CollatzResearch.WordTrace]
  refine ⟨40396706617934122559332499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107724550981157660158219997 40396706617934122559332499)
  ·
    refine ⟨60595059926901183838998749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40396706617934122559332499 60595059926901183838998749)
    ·
      refine ⟨22723147472587943939624531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60595059926901183838998749 22723147472587943939624531)
      ·
        refine ⟨34084721208881915909436797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22723147472587943939624531 34084721208881915909436797)
        ·
          refine ⟨12781770453330718466038799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34084721208881915909436797 12781770453330718466038799)
          ·
            refine ⟨19172655679996077699058199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12781770453330718466038799 19172655679996077699058199)
            ·
              refine ⟨28758983519994116548587299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19172655679996077699058199 28758983519994116548587299)
              ·
                refine ⟨43138475279991174822880949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28758983519994116548587299 43138475279991174822880949)
                ·
                  refine ⟨4044232057499172639645089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43138475279991174822880949 4044232057499172639645089)
                  ·
                    refine ⟨3033174043124379479733817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4044232057499172639645089 3033174043124379479733817)
                    ·
                      refine ⟨2274880532343284609800363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3033174043124379479733817 2274880532343284609800363)
                      ·
                        rfl

theorem cell23_4430314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 5, 2, 2].length) (baseStart_4430314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4430314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4430314 prefixEnd_4430314 := by exact prefixLift 4430314
  have htrace : WordTrace (prefixWord ++ tailWord_4430314) baseStart_4430314 baseEnd_4430314 := by
    simpa [prefixWord, tailWord_4430314, baseEnd_4430314] using wordTrace_append hprefix tailTrace_4430314
  have hstable : (prefixWord ++ tailWord_4430314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4430314).length < 2 ^ (prefixWord ++ tailWord_4430314).sum := by decide
  have hdescent : baseEnd_4430314 < baseStart_4430314 := by decide
  rcases family_descends (prefixWord ++ tailWord_4430314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4430320 : List Nat := [2, 1, 1, 1, 3, 3, 5, 7]
def baseStart_4430320 : Nat := 118140960795 + 4430320 * 2 ^ 59
def prefixEnd_4430320 : Nat := 4983230072969 + 3 ^ 40 * 4430320 * 2
def baseEnd_4430320 : Nat := 84254948638044873567605

theorem tailTrace_4430320 : CollatzResearch.WordTrace tailWord_4430320 prefixEnd_4430320 84254948638044873567605 := by
  unfold tailWord_4430320
  simp only [CollatzResearch.WordTrace]
  refine ⟨80793522654857376631024207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107724696873143168841365609 80793522654857376631024207)
  ·
    refine ⟨121190283982286064946536311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80793522654857376631024207 121190283982286064946536311)
    ·
      refine ⟨181785425973429097419804467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121190283982286064946536311 181785425973429097419804467)
      ·
        refine ⟨272678138960143646129706701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181785425973429097419804467 272678138960143646129706701)
        ·
          refine ⟨102254302110053867298640013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 272678138960143646129706701 102254302110053867298640013)
          ·
            refine ⟨38345363291270200236990005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102254302110053867298640013 38345363291270200236990005)
            ·
              refine ⟨3594877808556581272217813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38345363291270200236990005 3594877808556581272217813)
              ·
                refine ⟨84254948638044873567605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3594877808556581272217813 84254948638044873567605)
                ·
                  rfl

theorem cell23_4430320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5, 7].length) (baseStart_4430320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4430320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4430320 prefixEnd_4430320 := by exact prefixLift 4430320
  have htrace : WordTrace (prefixWord ++ tailWord_4430320) baseStart_4430320 baseEnd_4430320 := by
    simpa [prefixWord, tailWord_4430320, baseEnd_4430320] using wordTrace_append hprefix tailTrace_4430320
  have hstable : (prefixWord ++ tailWord_4430320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4430320).length < 2 ^ (prefixWord ++ tailWord_4430320).sum := by decide
  have hdescent : baseEnd_4430320 < baseStart_4430320 := by decide
  rcases family_descends (prefixWord ++ tailWord_4430320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4430330 : List Nat := [3, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3]
def baseStart_4430330 : Nat := 118140960795 + 4430330 * 2 ^ 59
def prefixEnd_4430330 : Nat := 4983230072969 + 3 ^ 40 * 4430330 * 2
def baseEnd_4430330 : Nat := 2274888748033756547200289

theorem tailTrace_4430330 : CollatzResearch.WordTrace tailWord_4430330 prefixEnd_4430330 2274888748033756547200289 := by
  unfold tailWord_4430330
  simp only [CollatzResearch.WordTrace]
  refine ⟨40396852509919631242478111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107724940026452349979941629 40396852509919631242478111)
  ·
    refine ⟨60595278764879446863717167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40396852509919631242478111 60595278764879446863717167)
    ·
      refine ⟨90892918147319170295575751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60595278764879446863717167 90892918147319170295575751)
      ·
        refine ⟨136339377220978755443363627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90892918147319170295575751 136339377220978755443363627)
        ·
          refine ⟨204509065831468133165045441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136339377220978755443363627 204509065831468133165045441)
          ·
            refine ⟨153381799373601099873784081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 204509065831468133165045441 153381799373601099873784081)
            ·
              refine ⟨115036349530200824905338061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 153381799373601099873784081 115036349530200824905338061)
              ·
                refine ⟨43138631073825309339501773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 115036349530200824905338061 43138631073825309339501773)
                ·
                  refine ⟨16176986652684491002313165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43138631073825309339501773 16176986652684491002313165)
                  ·
                    refine ⟨6066369994756684125867437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16176986652684491002313165 6066369994756684125867437)
                    ·
                      refine ⟨2274888748033756547200289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6066369994756684125867437 2274888748033756547200289)
                      ·
                        rfl

theorem cell23_4430330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3].length) (baseStart_4430330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4430330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4430330 prefixEnd_4430330 := by exact prefixLift 4430330
  have htrace : WordTrace (prefixWord ++ tailWord_4430330) baseStart_4430330 baseEnd_4430330 := by
    simpa [prefixWord, tailWord_4430330, baseEnd_4430330] using wordTrace_append hprefix tailTrace_4430330
  have hstable : (prefixWord ++ tailWord_4430330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4430330).length < 2 ^ (prefixWord ++ tailWord_4430330).sum := by decide
  have hdescent : baseEnd_4430330 < baseStart_4430330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4430330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4430364 : List Nat := [2, 2, 3, 1, 2, 4, 1, 1, 1, 3, 3]
def baseStart_4430364 : Nat := 118140960795 + 4430364 * 2 ^ 59
def prefixEnd_4430364 : Nat := 4983230072969 + 3 ^ 40 * 4430364 * 2
def baseEnd_4430364 : Nat := 2274906206376009414175133

theorem tailTrace_4430364 : CollatzResearch.WordTrace tailWord_4430364 prefixEnd_4430364 2274906206376009414175133 := by
  unfold tailWord_4430364
  simp only [CollatzResearch.WordTrace]
  refine ⟨80794325060777674388325073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107725766747703565851100097 80794325060777674388325073)
  ·
    refine ⟨60595743795583255791243805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80794325060777674388325073 60595743795583255791243805)
    ·
      refine ⟨22723403923343720921716427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60595743795583255791243805 22723403923343720921716427)
      ·
        refine ⟨34085105885015581382574641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22723403923343720921716427 34085105885015581382574641)
        ·
          refine ⟨25563829413761686036930981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34085105885015581382574641 25563829413761686036930981)
          ·
            refine ⟨4793218015080316131924559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25563829413761686036930981 4793218015080316131924559)
            ·
              refine ⟨7189827022620474197886839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4793218015080316131924559 7189827022620474197886839)
              ·
                refine ⟨10784740533930711296830259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7189827022620474197886839 10784740533930711296830259)
                ·
                  refine ⟨16177110800896066945245389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10784740533930711296830259 16177110800896066945245389)
                  ·
                    refine ⟨6066416550336025104467021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16177110800896066945245389 6066416550336025104467021)
                    ·
                      refine ⟨2274906206376009414175133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6066416550336025104467021 2274906206376009414175133)
                      ·
                        rfl

theorem cell23_4430364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 1, 1, 3, 3].length) (baseStart_4430364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4430364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4430364 prefixEnd_4430364 := by exact prefixLift 4430364
  have htrace : WordTrace (prefixWord ++ tailWord_4430364) baseStart_4430364 baseEnd_4430364 := by
    simpa [prefixWord, tailWord_4430364, baseEnd_4430364] using wordTrace_append hprefix tailTrace_4430364
  have hstable : (prefixWord ++ tailWord_4430364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4430364).length < 2 ^ (prefixWord ++ tailWord_4430364).sum := by decide
  have hdescent : baseEnd_4430364 < baseStart_4430364 := by decide
  rcases family_descends (prefixWord ++ tailWord_4430364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4430382 : List Nat := [4, 1, 3, 1, 4, 1, 1, 3, 1, 2, 2]
def baseStart_4430382 : Nat := 118140960795 + 4430382 * 2 ^ 59
def prefixEnd_4430382 : Nat := 4983230072969 + 3 ^ 40 * 4430382 * 2
def baseEnd_4430382 : Nat := 2274915449027790343750051

theorem tailTrace_4430382 : CollatzResearch.WordTrace tailWord_4430382 prefixEnd_4430382 2274915449027790343750051 := by
  unfold tailWord_4430382
  simp only [CollatzResearch.WordTrace]
  refine ⟨20198663329436267231350675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107726204423660091900536933 20198663329436267231350675)
  ·
    refine ⟨30297994994154400847026013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20198663329436267231350675 30297994994154400847026013)
    ·
      refine ⟨11361748122807900317634755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30297994994154400847026013 11361748122807900317634755)
      ·
        refine ⟨17042622184211850476452133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11361748122807900317634755 17042622184211850476452133)
        ·
          refine ⟨3195491659539721964334775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17042622184211850476452133 3195491659539721964334775)
          ·
            refine ⟨4793237489309582946502163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3195491659539721964334775 4793237489309582946502163)
            ·
              refine ⟨7189856233964374419753245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4793237489309582946502163 7189856233964374419753245)
              ·
                refine ⟨2696196087736640407407467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7189856233964374419753245 2696196087736640407407467)
                ·
                  refine ⟨4044294131604960611111201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2696196087736640407407467 4044294131604960611111201)
                  ·
                    refine ⟨3033220598703720458333401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4044294131604960611111201 3033220598703720458333401)
                    ·
                      refine ⟨2274915449027790343750051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3033220598703720458333401 2274915449027790343750051)
                      ·
                        rfl

theorem cell23_4430382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_4430382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4430382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4430382 prefixEnd_4430382 := by exact prefixLift 4430382
  have htrace : WordTrace (prefixWord ++ tailWord_4430382) baseStart_4430382 baseEnd_4430382 := by
    simpa [prefixWord, tailWord_4430382, baseEnd_4430382] using wordTrace_append hprefix tailTrace_4430382
  have hstable : (prefixWord ++ tailWord_4430382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4430382).length < 2 ^ (prefixWord ++ tailWord_4430382).sum := by decide
  have hdescent : baseEnd_4430382 < baseStart_4430382 := by decide
  rcases family_descends (prefixWord ++ tailWord_4430382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4430387 : List Nat := [1, 1, 1, 2, 4, 2, 2, 1, 3, 4, 2]
def baseStart_4430387 : Nat := 118140960795 + 4430387 * 2 ^ 59
def prefixEnd_4430387 : Nat := 4983230072969 + 3 ^ 40 * 4430387 * 2
def baseEnd_4430387 : Nat := 2274918016431062824187527

theorem tailTrace_4430387 : CollatzResearch.WordTrace tailWord_4430387 prefixEnd_4430387 2274918016431062824187527 := by
  unfold tailWord_4430387
  simp only [CollatzResearch.WordTrace]
  refine ⟨161589489000472023704737415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107726326000314682469824943 161589489000472023704737415)
  ·
    refine ⟨242384233500708035557106123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161589489000472023704737415 242384233500708035557106123)
    ·
      refine ⟨363576350251062053335659185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242384233500708035557106123 363576350251062053335659185)
      ·
        refine ⟨272682262688296540001744389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 363576350251062053335659185 272682262688296540001744389)
        ·
          refine ⟨51127924254055601250327073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 272682262688296540001744389 51127924254055601250327073)
          ·
            refine ⟨38345943190541700937745305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51127924254055601250327073 38345943190541700937745305)
            ·
              refine ⟨28759457392906275703308979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38345943190541700937745305 28759457392906275703308979)
              ·
                refine ⟨43139186089359413554963469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28759457392906275703308979 43139186089359413554963469)
                ·
                  refine ⟨16177194783509780083111301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43139186089359413554963469 16177194783509780083111301)
                  ·
                    refine ⟨3033224021908083765583369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16177194783509780083111301 3033224021908083765583369)
                    ·
                      refine ⟨2274918016431062824187527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3033224021908083765583369 2274918016431062824187527)
                      ·
                        rfl

theorem cell23_4430387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 3, 4, 2].length) (baseStart_4430387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4430387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4430387 prefixEnd_4430387 := by exact prefixLift 4430387
  have htrace : WordTrace (prefixWord ++ tailWord_4430387) baseStart_4430387 baseEnd_4430387 := by
    simpa [prefixWord, tailWord_4430387, baseEnd_4430387] using wordTrace_append hprefix tailTrace_4430387
  have hstable : (prefixWord ++ tailWord_4430387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4430387).length < 2 ^ (prefixWord ++ tailWord_4430387).sum := by decide
  have hdescent : baseEnd_4430387 < baseStart_4430387 := by decide
  rcases family_descends (prefixWord ++ tailWord_4430387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4430400 : List Nat := [2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 4]
def baseStart_4430400 : Nat := 118140960795 + 4430400 * 2 ^ 59
def prefixEnd_4430400 : Nat := 4983230072969 + 3 ^ 40 * 4430400 * 2
def baseEnd_4430400 : Nat := 2274924691679571273324967

theorem tailTrace_4430400 : CollatzResearch.WordTrace tailWord_4430400 prefixEnd_4430400 2274924691679571273324967 := by
  unfold tailWord_4430400
  simp only [CollatzResearch.WordTrace]
  refine ⟨80794981574712463462480327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107726642099616617949973769 80794981574712463462480327)
  ·
    refine ⟨121192472362068695193720491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80794981574712463462480327 121192472362068695193720491)
    ·
      refine ⟨181788708543103042790580737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121192472362068695193720491 181788708543103042790580737)
      ·
        refine ⟨136341531407327282092935553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181788708543103042790580737 136341531407327282092935553)
        ·
          refine ⟨102256148555495461569701665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136341531407327282092935553 102256148555495461569701665)
          ·
            refine ⟨76692111416621596177276249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102256148555495461569701665 76692111416621596177276249)
            ·
              refine ⟨57519083562466197132957187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76692111416621596177276249 57519083562466197132957187)
              ·
                refine ⟨86278625343699295699435781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57519083562466197132957187 86278625343699295699435781)
                ·
                  refine ⟨16177242251943617943644209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 86278625343699295699435781 16177242251943617943644209)
                  ·
                    refine ⟨12132931688957713457733157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16177242251943617943644209 12132931688957713457733157)
                    ·
                      refine ⟨2274924691679571273324967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12132931688957713457733157 2274924691679571273324967)
                      ·
                        rfl

theorem cell23_4430400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 4].length) (baseStart_4430400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4430400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4430400 prefixEnd_4430400 := by exact prefixLift 4430400
  have htrace : WordTrace (prefixWord ++ tailWord_4430400) baseStart_4430400 baseEnd_4430400 := by
    simpa [prefixWord, tailWord_4430400, baseEnd_4430400] using wordTrace_append hprefix tailTrace_4430400
  have hstable : (prefixWord ++ tailWord_4430400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4430400).length < 2 ^ (prefixWord ++ tailWord_4430400).sum := by decide
  have hdescent : baseEnd_4430400 < baseStart_4430400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4430400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4430457 : List Nat := [1, 2, 1, 3, 3, 2, 2, 2, 2, 5]
def baseStart_4430457 : Nat := 118140960795 + 4430457 * 2 ^ 59
def prefixEnd_4430457 : Nat := 4983230072969 + 3 ^ 40 * 4430457 * 2
def baseEnd_4430457 : Nat := 758317986692292516770735

theorem tailTrace_4430457 : CollatzResearch.WordTrace tailWord_4430457 prefixEnd_4430457 758317986692292516770735 := by
  unfold tailWord_4430457
  simp only [CollatzResearch.WordTrace]
  refine ⟨161592042110218425659785625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107728028073478950439857083 161592042110218425659785625)
  ·
    refine ⟨121194031582663819244839219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161592042110218425659785625 121194031582663819244839219)
    ·
      refine ⟨181791047373995728867258829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121194031582663819244839219 181791047373995728867258829)
      ·
        refine ⟨68171642765248398325222061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 181791047373995728867258829 68171642765248398325222061)
        ·
          refine ⟨25564366036968149371958273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68171642765248398325222061 25564366036968149371958273)
          ·
            refine ⟨19173274527726112028968705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25564366036968149371958273 19173274527726112028968705)
            ·
              refine ⟨14379955895794584021726529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19173274527726112028968705 14379955895794584021726529)
              ·
                refine ⟨10784966921845938016294897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14379955895794584021726529 10784966921845938016294897)
                ·
                  refine ⟨8088725191384453512221173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10784966921845938016294897 8088725191384453512221173)
                  ·
                    refine ⟨758317986692292516770735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8088725191384453512221173 758317986692292516770735)
                    ·
                      rfl

theorem cell23_4430457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 2, 2, 5].length) (baseStart_4430457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4430457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4430457 prefixEnd_4430457 := by exact prefixLift 4430457
  have htrace : WordTrace (prefixWord ++ tailWord_4430457) baseStart_4430457 baseEnd_4430457 := by
    simpa [prefixWord, tailWord_4430457, baseEnd_4430457] using wordTrace_append hprefix tailTrace_4430457
  have hstable : (prefixWord ++ tailWord_4430457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4430457).length < 2 ^ (prefixWord ++ tailWord_4430457).sum := by decide
  have hdescent : baseEnd_4430457 < baseStart_4430457 := by decide
  rcases family_descends (prefixWord ++ tailWord_4430457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4430494 : List Nat := [4, 3, 1, 1, 1, 1, 3, 1, 1, 3, 4]
def baseStart_4430494 : Nat := 118140960795 + 4430494 * 2 ^ 59
def prefixEnd_4430494 : Nat := 4983230072969 + 3 ^ 40 * 4430494 * 2
def baseEnd_4430494 : Nat := 2274972958861093905549535

theorem tailTrace_4430494 : CollatzResearch.WordTrace tailWord_4430494 prefixEnd_4430494 2274972958861093905549535 := by
  unfold tailWord_4430494
  simp only [CollatzResearch.WordTrace]
  refine ⟨20199173951385547622360317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107728927740722920652588357 20199173951385547622360317)
  ·
    refine ⟨7574690231769580358385119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20199173951385547622360317 7574690231769580358385119)
    ·
      refine ⟨11362035347654370537577679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7574690231769580358385119 11362035347654370537577679)
      ·
        refine ⟨17043053021481555806366519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11362035347654370537577679 17043053021481555806366519)
        ·
          refine ⟨25564579532222333709549779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17043053021481555806366519 25564579532222333709549779)
          ·
            refine ⟨38346869298333500564324669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25564579532222333709549779 38346869298333500564324669)
            ·
              refine ⟨14380075986875062711621751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38346869298333500564324669 14380075986875062711621751)
              ·
                refine ⟨21570113980312594067432627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14380075986875062711621751 21570113980312594067432627)
                ·
                  refine ⟨32355170970468891101148941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21570113980312594067432627 32355170970468891101148941)
                  ·
                    refine ⟨12133189113925834162930853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32355170970468891101148941 12133189113925834162930853)
                    ·
                      refine ⟨2274972958861093905549535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12133189113925834162930853 2274972958861093905549535)
                      ·
                        rfl

theorem cell23_4430494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_4430494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4430494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4430494 prefixEnd_4430494 := by exact prefixLift 4430494
  have htrace : WordTrace (prefixWord ++ tailWord_4430494) baseStart_4430494 baseEnd_4430494 := by
    simpa [prefixWord, tailWord_4430494, baseEnd_4430494] using wordTrace_append hprefix tailTrace_4430494
  have hstable : (prefixWord ++ tailWord_4430494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4430494).length < 2 ^ (prefixWord ++ tailWord_4430494).sum := by decide
  have hdescent : baseEnd_4430494 < baseStart_4430494 := by decide
  rcases family_descends (prefixWord ++ tailWord_4430494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4430554 : List Nat := [3, 1, 1, 2, 2, 2, 1, 3, 1, 5, 2]
def baseStart_4430554 : Nat := 118140960795 + 4430554 * 2 ^ 59
def prefixEnd_4430554 : Nat := 4983230072969 + 3 ^ 40 * 4430554 * 2
def baseEnd_4430554 : Nat := 2275003767700363670799259

theorem tailTrace_4430554 : CollatzResearch.WordTrace tailWord_4430554 prefixEnd_4430554 2275003767700363670799259 := by
  unfold tailWord_4430554
  simp only [CollatzResearch.WordTrace]
  refine ⟨40398894997716752806516679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107730386660578007484044477 40398894997716752806516679)
  ·
    refine ⟨60598342496575129209775019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40398894997716752806516679 60598342496575129209775019)
    ·
      refine ⟨90897513744862693814662529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60598342496575129209775019 90897513744862693814662529)
      ·
        refine ⟨68173135308647020360996897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90897513744862693814662529 68173135308647020360996897)
        ·
          refine ⟨51129851481485265270747673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68173135308647020360996897 51129851481485265270747673)
          ·
            refine ⟨38347388611113948953060755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51129851481485265270747673 38347388611113948953060755)
            ·
              refine ⟨57521082916670923429591133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38347388611113948953060755 57521082916670923429591133)
              ·
                refine ⟨21570406093751596286096675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57521082916670923429591133 21570406093751596286096675)
                ·
                  refine ⟨32355609140627394429145013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21570406093751596286096675 32355609140627394429145013)
                  ·
                    refine ⟨3033338356933818227732345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32355609140627394429145013 3033338356933818227732345)
                    ·
                      refine ⟨2275003767700363670799259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3033338356933818227732345 2275003767700363670799259)
                      ·
                        rfl

theorem cell23_4430554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 1, 5, 2].length) (baseStart_4430554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4430554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4430554 prefixEnd_4430554 := by exact prefixLift 4430554
  have htrace : WordTrace (prefixWord ++ tailWord_4430554) baseStart_4430554 baseEnd_4430554 := by
    simpa [prefixWord, tailWord_4430554, baseEnd_4430554] using wordTrace_append hprefix tailTrace_4430554
  have hstable : (prefixWord ++ tailWord_4430554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4430554).length < 2 ^ (prefixWord ++ tailWord_4430554).sum := by decide
  have hdescent : baseEnd_4430554 < baseStart_4430554 := by decide
  rcases family_descends (prefixWord ++ tailWord_4430554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4430564 : List Nat := [2, 3, 1, 1, 1, 4, 2, 3, 1, 5]
def baseStart_4430564 : Nat := 118140960795 + 4430564 * 2 ^ 59
def prefixEnd_4430564 : Nat := 4983230072969 + 3 ^ 40 * 4430564 * 2
def baseEnd_4430564 : Nat := 758336300835636210558071

theorem tailTrace_4430564 : CollatzResearch.WordTrace tailWord_4430564 prefixEnd_4430564 758336300835636210558071 := by
  unfold tailWord_4430564
  simp only [CollatzResearch.WordTrace]
  refine ⟨80797972360415391466965373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107730629813887188622620497 80797972360415391466965373)
  ·
    refine ⟨30299239635155771800112015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80797972360415391466965373 30299239635155771800112015)
    ·
      refine ⟨45448859452733657700168023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30299239635155771800112015 45448859452733657700168023)
      ·
        refine ⟨68173289179100486550252035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45448859452733657700168023 68173289179100486550252035)
        ·
          refine ⟨102259933768650729825378053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68173289179100486550252035 102259933768650729825378053)
          ·
            refine ⟨19173737581622011842258385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 102259933768650729825378053 19173737581622011842258385)
            ·
              refine ⟨14380303186216508881693789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19173737581622011842258385 14380303186216508881693789)
              ·
                refine ⟨5392613694831190830635171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14380303186216508881693789 5392613694831190830635171)
                ·
                  refine ⟨8088920542246786245952757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5392613694831190830635171 8088920542246786245952757)
                  ·
                    refine ⟨758336300835636210558071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8088920542246786245952757 758336300835636210558071)
                    ·
                      rfl

theorem cell23_4430564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 3, 1, 5].length) (baseStart_4430564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4430564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4430564 prefixEnd_4430564 := by exact prefixLift 4430564
  have htrace : WordTrace (prefixWord ++ tailWord_4430564) baseStart_4430564 baseEnd_4430564 := by
    simpa [prefixWord, tailWord_4430564, baseEnd_4430564] using wordTrace_append hprefix tailTrace_4430564
  have hstable : (prefixWord ++ tailWord_4430564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4430564).length < 2 ^ (prefixWord ++ tailWord_4430564).sum := by decide
  have hdescent : baseEnd_4430564 < baseStart_4430564 := by decide
  rcases family_descends (prefixWord ++ tailWord_4430564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4430578 : List Nat := [3, 2, 1, 3, 1, 4, 1, 1, 3, 1, 3]
def baseStart_4430578 : Nat := 118140960795 + 4430578 * 2 ^ 59
def prefixEnd_4430578 : Nat := 4983230072969 + 3 ^ 40 * 4430578 * 2
def baseEnd_4430578 : Nat := 2275016091236071576899149

theorem tailTrace_4430578 : CollatzResearch.WordTrace tailWord_4430578 prefixEnd_4430578 2275016091236071576899149 := by
  unfold tailWord_4430578
  simp only [CollatzResearch.WordTrace]
  refine ⟨40399113835695015831235097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107730970228520042216626925 40399113835695015831235097)
  ·
    refine ⟨30299335376771261873426323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40399113835695015831235097 30299335376771261873426323)
    ·
      refine ⟨45449003065156892810139485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30299335376771261873426323 45449003065156892810139485)
      ·
        refine ⟨17043376149433834803802307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45449003065156892810139485 17043376149433834803802307)
        ·
          refine ⟨25565064224150752205703461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17043376149433834803802307 25565064224150752205703461)
          ·
            refine ⟨4793449542028266038569399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25565064224150752205703461 4793449542028266038569399)
            ·
              refine ⟨7190174313042399057854099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4793449542028266038569399 7190174313042399057854099)
              ·
                refine ⟨10785261469563598586781149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7190174313042399057854099 10785261469563598586781149)
                ·
                  refine ⟨4044473051086349470042931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10785261469563598586781149 4044473051086349470042931)
                  ·
                    refine ⟨6066709576629524205064397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4044473051086349470042931 6066709576629524205064397)
                    ·
                      refine ⟨2275016091236071576899149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6066709576629524205064397 2275016091236071576899149)
                      ·
                        rfl

theorem cell23_4430578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_4430578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4430578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4430578 prefixEnd_4430578 := by exact prefixLift 4430578
  have htrace : WordTrace (prefixWord ++ tailWord_4430578) baseStart_4430578 baseEnd_4430578 := by
    simpa [prefixWord, tailWord_4430578, baseEnd_4430578] using wordTrace_append hprefix tailTrace_4430578
  have hstable : (prefixWord ++ tailWord_4430578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4430578).length < 2 ^ (prefixWord ++ tailWord_4430578).sum := by decide
  have hdescent : baseEnd_4430578 < baseStart_4430578 := by decide
  rcases family_descends (prefixWord ++ tailWord_4430578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4430597 : List Nat := [1, 3, 1, 1, 2, 1, 1, 2, 5, 2, 4]
def baseStart_4430597 : Nat := 118140960795 + 4430597 * 2 ^ 59
def prefixEnd_4430597 : Nat := 4983230072969 + 3 ^ 40 * 4430597 * 2
def baseEnd_4430597 : Nat := 2275025847368507002561561

theorem tailTrace_4430597 : CollatzResearch.WordTrace tailWord_4430597 prefixEnd_4430597 2275025847368507002561561 := by
  unfold tailWord_4430597
  simp only [CollatzResearch.WordTrace]
  refine ⟨161597148329711229569882045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107731432219807486379921363 161597148329711229569882045)
  ·
    refine ⟨60598930623641711088705767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161597148329711229569882045 60598930623641711088705767)
    ·
      refine ⟨90898395935462566633058651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60598930623641711088705767 90898395935462566633058651)
      ·
        refine ⟨136347593903193849949587977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90898395935462566633058651 136347593903193849949587977)
        ·
          refine ⟨102260695427395387462190983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136347593903193849949587977 102260695427395387462190983)
          ·
            refine ⟨153391043141093081193286475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102260695427395387462190983 153391043141093081193286475)
            ·
              refine ⟨230086564711639621789929713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153391043141093081193286475 230086564711639621789929713)
              ·
                refine ⟨172564923533729716342447285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 230086564711639621789929713 172564923533729716342447285)
                ·
                  refine ⟨16177961581287160907104433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 172564923533729716342447285 16177961581287160907104433)
                  ·
                    refine ⟨12133471185965370680328325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16177961581287160907104433 12133471185965370680328325)
                    ·
                      refine ⟨2275025847368507002561561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12133471185965370680328325 2275025847368507002561561)
                      ·
                        rfl

theorem cell23_4430597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5, 2, 4].length) (baseStart_4430597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4430597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4430597 prefixEnd_4430597 := by exact prefixLift 4430597
  have htrace : WordTrace (prefixWord ++ tailWord_4430597) baseStart_4430597 baseEnd_4430597 := by
    simpa [prefixWord, tailWord_4430597, baseEnd_4430597] using wordTrace_append hprefix tailTrace_4430597
  have hstable : (prefixWord ++ tailWord_4430597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4430597).length < 2 ^ (prefixWord ++ tailWord_4430597).sum := by decide
  have hdescent : baseEnd_4430597 < baseStart_4430597 := by decide
  rcases family_descends (prefixWord ++ tailWord_4430597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4430601 : List Nat := [1, 2, 1, 1, 3, 2, 2, 4, 3, 2, 2]
def baseStart_4430601 : Nat := 118140960795 + 4430601 * 2 ^ 59
def prefixEnd_4430601 : Nat := 4983230072969 + 3 ^ 40 * 4430601 * 2
def baseEnd_4430601 : Nat := 2275027901291124986911543

theorem tailTrace_4430601 : CollatzResearch.WordTrace tailWord_4430601 prefixEnd_4430601 2275027901291124986911543 := by
  unfold tailWord_4430601
  simp only [CollatzResearch.WordTrace]
  refine ⟨161597294221696738253027657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107731529481131158835351771 161597294221696738253027657)
  ·
    refine ⟨121197970666272553689770743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161597294221696738253027657 121197970666272553689770743)
    ·
      refine ⟨181796955999408830534656115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121197970666272553689770743 181796955999408830534656115)
      ·
        refine ⟨272695433999113245801984173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181796955999408830534656115 272695433999113245801984173)
        ·
          refine ⟨102260787749667467175744065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 272695433999113245801984173 102260787749667467175744065)
          ·
            refine ⟨76695590812250600381808049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102260787749667467175744065 76695590812250600381808049)
            ·
              refine ⟨57521693109187950286356037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76695590812250600381808049 57521693109187950286356037)
              ·
                refine ⟨10785317457972740678691757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57521693109187950286356037 10785317457972740678691757)
                ·
                  refine ⟨4044494046739777754509409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10785317457972740678691757 4044494046739777754509409)
                  ·
                    refine ⟨3033370535054833315882057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4044494046739777754509409 3033370535054833315882057)
                    ·
                      refine ⟨2275027901291124986911543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3033370535054833315882057 2275027901291124986911543)
                      ·
                        rfl

theorem cell23_4430601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4, 3, 2, 2].length) (baseStart_4430601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4430601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4430601 prefixEnd_4430601 := by exact prefixLift 4430601
  have htrace : WordTrace (prefixWord ++ tailWord_4430601) baseStart_4430601 baseEnd_4430601 := by
    simpa [prefixWord, tailWord_4430601, baseEnd_4430601] using wordTrace_append hprefix tailTrace_4430601
  have hstable : (prefixWord ++ tailWord_4430601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4430601).length < 2 ^ (prefixWord ++ tailWord_4430601).sum := by decide
  have hdescent : baseEnd_4430601 < baseStart_4430601 := by decide
  rcases family_descends (prefixWord ++ tailWord_4430601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4430628 : List Nat := [2, 3, 1, 3, 3, 1, 2, 2, 2, 4]
def baseStart_4430628 : Nat := 118140960795 + 4430628 * 2 ^ 59
def prefixEnd_4430628 : Nat := 4983230072969 + 3 ^ 40 * 4430628 * 2
def baseEnd_4430628 : Nat := 758347255089598793757973

theorem tailTrace_4430628 : CollatzResearch.WordTrace tailWord_4430628 prefixEnd_4430628 758347255089598793757973 := by
  unfold tailWord_4430628
  simp only [CollatzResearch.WordTrace]
  refine ⟨80799139496299460932130269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107732185995065947909507025 80799139496299460932130269)
  ·
    refine ⟨30299677311112297849548851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80799139496299460932130269 30299677311112297849548851)
    ·
      refine ⟨45449515966668446774323277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30299677311112297849548851 45449515966668446774323277)
      ·
        refine ⟨17043568487500667540371229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45449515966668446774323277 17043568487500667540371229)
        ·
          refine ⟨6391338182812750327639211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17043568487500667540371229 6391338182812750327639211)
          ·
            refine ⟨9587007274219125491458817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6391338182812750327639211 9587007274219125491458817)
            ·
              refine ⟨7190255455664344118594113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9587007274219125491458817 7190255455664344118594113)
              ·
                refine ⟨5392691591748258088945585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7190255455664344118594113 5392691591748258088945585)
                ·
                  refine ⟨4044518693811193566709189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5392691591748258088945585 4044518693811193566709189)
                  ·
                    refine ⟨758347255089598793757973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4044518693811193566709189 758347255089598793757973)
                    ·
                      rfl

theorem cell23_4430628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 2, 2, 4].length) (baseStart_4430628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4430628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4430628 prefixEnd_4430628 := by exact prefixLift 4430628
  have htrace : WordTrace (prefixWord ++ tailWord_4430628) baseStart_4430628 baseEnd_4430628 := by
    simpa [prefixWord, tailWord_4430628, baseEnd_4430628] using wordTrace_append hprefix tailTrace_4430628
  have hstable : (prefixWord ++ tailWord_4430628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4430628).length < 2 ^ (prefixWord ++ tailWord_4430628).sum := by decide
  have hdescent : baseEnd_4430628 < baseStart_4430628 := by decide
  rcases family_descends (prefixWord ++ tailWord_4430628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4430669 : List Nat := [1, 6, 1, 2, 2, 1, 2, 3, 1, 2, 2]
def baseStart_4430669 : Nat := 118140960795 + 4430669 * 2 ^ 59
def prefixEnd_4430669 : Nat := 4983230072969 + 3 ^ 40 * 4430669 * 2
def baseEnd_4430669 : Nat := 2275062817975630720861231

theorem tailTrace_4430669 : CollatzResearch.WordTrace tailWord_4430669 prefixEnd_4430669 2275062817975630720861231 := by
  unfold tailWord_4430669
  simp only [CollatzResearch.WordTrace]
  refine ⟨161599774385450385866503061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107733182923633590577668707 161599774385450385866503061)
  ·
    refine ⟨7574989424317986837492331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 161599774385450385866503061 7574989424317986837492331)
    ·
      refine ⟨11362484136476980256238497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7574989424317986837492331 11362484136476980256238497)
      ·
        refine ⟨8521863102357735192178873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11362484136476980256238497 8521863102357735192178873)
        ·
          refine ⟨6391397326768301394134155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8521863102357735192178873 6391397326768301394134155)
          ·
            refine ⟨9587095990152452091201233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6391397326768301394134155 9587095990152452091201233)
            ·
              refine ⟨7190321992614339068400925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9587095990152452091201233 7190321992614339068400925)
              ·
                refine ⟨2696370747230377150650347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7190321992614339068400925 2696370747230377150650347)
                ·
                  refine ⟨4044556120845565725975521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2696370747230377150650347 4044556120845565725975521)
                  ·
                    refine ⟨3033417090634174294481641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4044556120845565725975521 3033417090634174294481641)
                    ·
                      refine ⟨2275062817975630720861231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3033417090634174294481641 2275062817975630720861231)
                      ·
                        rfl

theorem cell23_4430669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_4430669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4430669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4430669 prefixEnd_4430669 := by exact prefixLift 4430669
  have htrace : WordTrace (prefixWord ++ tailWord_4430669) baseStart_4430669 baseEnd_4430669 := by
    simpa [prefixWord, tailWord_4430669, baseEnd_4430669] using wordTrace_append hprefix tailTrace_4430669
  have hstable : (prefixWord ++ tailWord_4430669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4430669).length < 2 ^ (prefixWord ++ tailWord_4430669).sum := by decide
  have hdescent : baseEnd_4430669 < baseStart_4430669 := by decide
  rcases family_descends (prefixWord ++ tailWord_4430669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4430702 : List Nat := [4, 1, 2, 3, 2, 1, 3, 1, 2, 1, 3]
def baseStart_4430702 : Nat := 118140960795 + 4430702 * 2 ^ 59
def prefixEnd_4430702 : Nat := 4983230072969 + 3 ^ 40 * 4430702 * 2
def baseEnd_4430702 : Nat := 2275079762837229091748579

theorem tailTrace_4430702 : CollatzResearch.WordTrace tailWord_4430702 prefixEnd_4430702 2275079762837229091748579 := by
  unfold tailWord_4430702
  simp only [CollatzResearch.WordTrace]
  refine ⟨20200122249291354062806795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107733985329553888334969573 20200122249291354062806795)
  ·
    refine ⟨30300183373937031094210193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20200122249291354062806795 30300183373937031094210193)
    ·
      refine ⟨22725137530452773320657645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30300183373937031094210193 22725137530452773320657645)
      ·
        refine ⟨8521926573919789995246617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22725137530452773320657645 8521926573919789995246617)
        ·
          refine ⟨6391444930439842496434963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8521926573919789995246617 6391444930439842496434963)
          ·
            refine ⟨9587167395659763744652445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6391444930439842496434963 9587167395659763744652445)
            ·
              refine ⟨3595187773372411404244667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9587167395659763744652445 3595187773372411404244667)
              ·
                refine ⟨5392781660058617106367001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3595187773372411404244667 5392781660058617106367001)
                ·
                  refine ⟨4044586245043962829775251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5392781660058617106367001 4044586245043962829775251)
                  ·
                    refine ⟨6066879367565944244662877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4044586245043962829775251 6066879367565944244662877)
                    ·
                      refine ⟨2275079762837229091748579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6066879367565944244662877 2275079762837229091748579)
                      ·
                        rfl

theorem cell23_4430702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_4430702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4430702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4430702 prefixEnd_4430702 := by exact prefixLift 4430702
  have htrace : WordTrace (prefixWord ++ tailWord_4430702) baseStart_4430702 baseEnd_4430702 := by
    simpa [prefixWord, tailWord_4430702, baseEnd_4430702] using wordTrace_append hprefix tailTrace_4430702
  have hstable : (prefixWord ++ tailWord_4430702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4430702).length < 2 ^ (prefixWord ++ tailWord_4430702).sum := by decide
  have hdescent : baseEnd_4430702 < baseStart_4430702 := by decide
  rcases family_descends (prefixWord ++ tailWord_4430702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4430704 : List Nat := [2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 4]
def baseStart_4430704 : Nat := 118140960795 + 4430704 * 2 ^ 59
def prefixEnd_4430704 : Nat := 4983230072969 + 3 ^ 40 * 4430704 * 2
def baseEnd_4430704 : Nat := 2275080789798538083923569

theorem tailTrace_4430704 : CollatzResearch.WordTrace tailWord_4430704 prefixEnd_4430704 2275080789798538083923569 := by
  unfold tailWord_4430704
  simp only [CollatzResearch.WordTrace]
  refine ⟨80800525470161793422013583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107734033960215724562684777 80800525470161793422013583)
  ·
    refine ⟨121200788205242690133020375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80800525470161793422013583 121200788205242690133020375)
    ·
      refine ⟨181801182307864035199530563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121200788205242690133020375 181801182307864035199530563)
      ·
        refine ⟨272701773461796052799295845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181801182307864035199530563 272701773461796052799295845)
        ·
          refine ⟨51131582524086759899867971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 272701773461796052799295845 51131582524086759899867971)
          ·
            refine ⟨76697373786130139849801957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51131582524086759899867971 76697373786130139849801957)
            ·
              refine ⟨14380757584899401221837867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76697373786130139849801957 14380757584899401221837867)
              ·
                refine ⟨21571136377349101832756801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14380757584899401221837867 21571136377349101832756801)
                ·
                  refine ⟨16178352283011826374567601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21571136377349101832756801 16178352283011826374567601)
                  ·
                    refine ⟨12133764212258869780925701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16178352283011826374567601 12133764212258869780925701)
                    ·
                      refine ⟨2275080789798538083923569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12133764212258869780925701 2275080789798538083923569)
                      ·
                        rfl

theorem cell23_4430704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 4].length) (baseStart_4430704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4430704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4430704 prefixEnd_4430704 := by exact prefixLift 4430704
  have htrace : WordTrace (prefixWord ++ tailWord_4430704) baseStart_4430704 baseEnd_4430704 := by
    simpa [prefixWord, tailWord_4430704, baseEnd_4430704] using wordTrace_append hprefix tailTrace_4430704
  have hstable : (prefixWord ++ tailWord_4430704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4430704).length < 2 ^ (prefixWord ++ tailWord_4430704).sum := by decide
  have hdescent : baseEnd_4430704 < baseStart_4430704 := by decide
  rcases family_descends (prefixWord ++ tailWord_4430704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4430731 : List Nat := [1, 1, 1, 1, 4, 2, 5, 3, 5]
def baseStart_4430731 : Nat := 118140960795 + 4430731 * 2 ^ 59
def prefixEnd_4430731 : Nat := 4983230072969 + 3 ^ 40 * 4430731 * 2
def baseEnd_4430731 : Nat := 252788294864023275365105

theorem tailTrace_4430731 : CollatzResearch.WordTrace tailWord_4430731 prefixEnd_4430731 252788294864023275365105 := by
  unfold tailWord_4430731
  simp only [CollatzResearch.WordTrace]
  refine ⟨161602035711225770455260047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107734690474150513636840031 161602035711225770455260047)
  ·
    refine ⟨242403053566838655682890071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161602035711225770455260047 242403053566838655682890071)
    ·
      refine ⟨363604580350257983524335107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242403053566838655682890071 363604580350257983524335107)
      ·
        refine ⟨545406870525386975286502661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 363604580350257983524335107 545406870525386975286502661)
        ·
          refine ⟨102263788223510057866219249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 545406870525386975286502661 102263788223510057866219249)
          ·
            refine ⟨76697841167632543399664437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102263788223510057866219249 76697841167632543399664437)
            ·
              refine ⟨7190422609465550943718541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76697841167632543399664437 7190422609465550943718541)
              ·
                refine ⟨2696408478549581603894453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7190422609465550943718541 2696408478549581603894453)
                ·
                  refine ⟨252788294864023275365105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2696408478549581603894453 252788294864023275365105)
                  ·
                    rfl

theorem cell23_4430731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 3, 5].length) (baseStart_4430731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4430731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4430731 prefixEnd_4430731 := by exact prefixLift 4430731
  have htrace : WordTrace (prefixWord ++ tailWord_4430731) baseStart_4430731 baseEnd_4430731 := by
    simpa [prefixWord, tailWord_4430731, baseEnd_4430731] using wordTrace_append hprefix tailTrace_4430731
  have hstable : (prefixWord ++ tailWord_4430731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4430731).length < 2 ^ (prefixWord ++ tailWord_4430731).sum := by decide
  have hdescent : baseEnd_4430731 < baseStart_4430731 := by decide
  rcases family_descends (prefixWord ++ tailWord_4430731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4430748 : List Nat := [2, 2, 3, 3, 2, 2, 1, 1, 7]
def baseStart_4430748 : Nat := 118140960795 + 4430748 * 2 ^ 59
def prefixEnd_4430748 : Nat := 4983230072969 + 3 ^ 40 * 4430748 * 2
def baseEnd_4430748 : Nat := 252789264771926212419263

theorem tailTrace_4430748 : CollatzResearch.WordTrace tailWord_4430748 prefixEnd_4430748 252789264771926212419263 := by
  unfold tailWord_4430748
  simp only [CollatzResearch.WordTrace]
  refine ⟨80801327876082091179314449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107735103834776121572419265 80801327876082091179314449)
  ·
    refine ⟨60600995907061568384485837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80801327876082091179314449 60600995907061568384485837)
    ·
      refine ⟨22725373465148088144182189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60600995907061568384485837 22725373465148088144182189)
      ·
        refine ⟨8522015049430533054068321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22725373465148088144182189 8522015049430533054068321)
        ·
          refine ⟨6391511287072899790551241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8522015049430533054068321 6391511287072899790551241)
          ·
            refine ⟨4793633465304674842913431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6391511287072899790551241 4793633465304674842913431)
            ·
              refine ⟨7190450197957012264370147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4793633465304674842913431 7190450197957012264370147)
              ·
                refine ⟨10785675296935518396555221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7190450197957012264370147 10785675296935518396555221)
                ·
                  refine ⟨252789264771926212419263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10785675296935518396555221 252789264771926212419263)
                  ·
                    rfl

theorem cell23_4430748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 1, 7].length) (baseStart_4430748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4430748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4430748 prefixEnd_4430748 := by exact prefixLift 4430748
  have htrace : WordTrace (prefixWord ++ tailWord_4430748) baseStart_4430748 baseEnd_4430748 := by
    simpa [prefixWord, tailWord_4430748, baseEnd_4430748] using wordTrace_append hprefix tailTrace_4430748
  have hstable : (prefixWord ++ tailWord_4430748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4430748).length < 2 ^ (prefixWord ++ tailWord_4430748).sum := by decide
  have hdescent : baseEnd_4430748 < baseStart_4430748 := by decide
  rcases family_descends (prefixWord ++ tailWord_4430748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4430759 : List Nat := [1, 1, 6, 1, 3, 2, 2, 1, 2, 2, 2]
def baseStart_4430759 : Nat := 118140960795 + 4430759 * 2 ^ 59
def prefixEnd_4430759 : Nat := 4983230072969 + 3 ^ 40 * 4430759 * 2
def baseEnd_4430759 : Nat := 2275109031234535368735817

theorem tailTrace_4430759 : CollatzResearch.WordTrace tailWord_4430759 prefixEnd_4430759 2275109031234535368735817 := by
  unfold tailWord_4430759
  simp only [CollatzResearch.WordTrace]
  refine ⟨161603056955124331237279331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107735371303416220824852887 161603056955124331237279331)
  ·
    refine ⟨242404585432686496855918997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161603056955124331237279331 242404585432686496855918997)
    ·
      refine ⟨11362714942157179540121203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 242404585432686496855918997 11362714942157179540121203)
      ·
        refine ⟨17044072413235769310181805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11362714942157179540121203 17044072413235769310181805)
        ·
          refine ⟨6391527154963413491318177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17044072413235769310181805 6391527154963413491318177)
          ·
            refine ⟨4793645366222560118488633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6391527154963413491318177 4793645366222560118488633)
            ·
              refine ⟨3595234024666920088866475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4793645366222560118488633 3595234024666920088866475)
              ·
                refine ⟨5392851037000380133299713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3595234024666920088866475 5392851037000380133299713)
                ·
                  refine ⟨4044638277750285099974785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5392851037000380133299713 4044638277750285099974785)
                  ·
                    refine ⟨3033478708312713824981089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4044638277750285099974785 3033478708312713824981089)
                    ·
                      refine ⟨2275109031234535368735817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3033478708312713824981089 2275109031234535368735817)
                      ·
                        rfl

theorem cell23_4430759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_4430759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4430759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4430759 prefixEnd_4430759 := by exact prefixLift 4430759
  have htrace : WordTrace (prefixWord ++ tailWord_4430759) baseStart_4430759 baseEnd_4430759 := by
    simpa [prefixWord, tailWord_4430759, baseEnd_4430759] using wordTrace_append hprefix tailTrace_4430759
  have hstable : (prefixWord ++ tailWord_4430759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4430759).length < 2 ^ (prefixWord ++ tailWord_4430759).sum := by decide
  have hdescent : baseEnd_4430759 < baseStart_4430759 := by decide
  rcases family_descends (prefixWord ++ tailWord_4430759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4430794 : List Nat := [3, 1, 2, 1, 2, 1, 1, 3, 2, 1, 6]
def baseStart_4430794 : Nat := 118140960795 + 4430794 * 2 ^ 59
def prefixEnd_4430794 : Nat := 4983230072969 + 3 ^ 40 * 4430794 * 2
def baseEnd_4430794 : Nat := 2275127003057442731798155

theorem tailTrace_4430794 : CollatzResearch.WordTrace tailWord_4430794 prefixEnd_4430794 2275127003057442731798155 := by
  unfold tailWord_4430794
  simp only [CollatzResearch.WordTrace]
  refine ⟨40401083377499383053700859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107736222339998354809868957 40401083377499383053700859)
  ·
    refine ⟨60601625066249074580551289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40401083377499383053700859 60601625066249074580551289)
    ·
      refine ⟨45451218799686805935413467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60601625066249074580551289 45451218799686805935413467)
      ·
        refine ⟨68176828199530208903120201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45451218799686805935413467 68176828199530208903120201)
        ·
          refine ⟨51132621149647656677340151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68176828199530208903120201 51132621149647656677340151)
          ·
            refine ⟨76698931724471485016010227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51132621149647656677340151 76698931724471485016010227)
            ·
              refine ⟨115048397586707227524015341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76698931724471485016010227 115048397586707227524015341)
              ·
                refine ⟨43143149095015210321505753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 115048397586707227524015341 43143149095015210321505753)
                ·
                  refine ⟨32357361821261407741129315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43143149095015210321505753 32357361821261407741129315)
                  ·
                    refine ⟨48536042731892111611693973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32357361821261407741129315 48536042731892111611693973)
                    ·
                      refine ⟨2275127003057442731798155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48536042731892111611693973 2275127003057442731798155)
                      ·
                        rfl

theorem cell23_4430794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_4430794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4430794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4430794 prefixEnd_4430794 := by exact prefixLift 4430794
  have htrace : WordTrace (prefixWord ++ tailWord_4430794) baseStart_4430794 baseEnd_4430794 := by
    simpa [prefixWord, tailWord_4430794, baseEnd_4430794] using wordTrace_append hprefix tailTrace_4430794
  have hstable : (prefixWord ++ tailWord_4430794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4430794).length < 2 ^ (prefixWord ++ tailWord_4430794).sum := by decide
  have hdescent : baseEnd_4430794 < baseStart_4430794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4430794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4430801 : List Nat := [1, 2, 2, 1, 2, 1, 3, 4, 2, 2, 3]
def baseStart_4430801 : Nat := 118140960795 + 4430801 * 2 ^ 59
def prefixEnd_4430801 : Nat := 4983230072969 + 3 ^ 40 * 4430801 * 2
def baseEnd_4430801 : Nat := 2275130597422024204410623

theorem tailTrace_4430801 : CollatzResearch.WordTrace tailWord_4430801 prefixEnd_4430801 2275130597422024204410623 := by
  unfold tailWord_4430801
  simp only [CollatzResearch.WordTrace]
  refine ⟨161604588820972172410308257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107736392547314781606872171 161604588820972172410308257)
  ·
    refine ⟨121203441615729129307731193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161604588820972172410308257 121203441615729129307731193)
    ·
      refine ⟨90902581211796846980798395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121203441615729129307731193 90902581211796846980798395)
      ·
        refine ⟨136353871817695270471197593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90902581211796846980798395 136353871817695270471197593)
        ·
          refine ⟨102265403863271452853398195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136353871817695270471197593 102265403863271452853398195)
          ·
            refine ⟨153398105794907179280097293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102265403863271452853398195 153398105794907179280097293)
            ·
              refine ⟨57524289673090192230036485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 153398105794907179280097293 57524289673090192230036485)
              ·
                refine ⟨10785804313704411043131841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57524289673090192230036485 10785804313704411043131841)
                ·
                  refine ⟨8089353235278308282348881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10785804313704411043131841 8089353235278308282348881)
                  ·
                    refine ⟨6067014926458731211761661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8089353235278308282348881 6067014926458731211761661)
                    ·
                      refine ⟨2275130597422024204410623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6067014926458731211761661 2275130597422024204410623)
                      ·
                        rfl

theorem cell23_4430801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4, 2, 2, 3].length) (baseStart_4430801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4430801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4430801 prefixEnd_4430801 := by exact prefixLift 4430801
  have htrace : WordTrace (prefixWord ++ tailWord_4430801) baseStart_4430801 baseEnd_4430801 := by
    simpa [prefixWord, tailWord_4430801, baseEnd_4430801] using wordTrace_append hprefix tailTrace_4430801
  have hstable : (prefixWord ++ tailWord_4430801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4430801).length < 2 ^ (prefixWord ++ tailWord_4430801).sum := by decide
  have hdescent : baseEnd_4430801 < baseStart_4430801 := by decide
  rcases family_descends (prefixWord ++ tailWord_4430801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4430901 : List Nat := [1, 3, 3, 1, 1, 1, 1, 3, 3, 2, 4]
def baseStart_4430901 : Nat := 118140960795 + 4430901 * 2 ^ 59
def prefixEnd_4430901 : Nat := 4983230072969 + 3 ^ 40 * 4430901 * 2
def baseEnd_4430901 : Nat := 2275181945487473813160163

theorem tailTrace_4430901 : CollatzResearch.WordTrace tailWord_4430901 prefixEnd_4430901 2275181945487473813160163 := by
  unfold tailWord_4430901
  simp only [CollatzResearch.WordTrace]
  refine ⟨161608236120609889488948557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107738824080406592992632371 161608236120609889488948557)
  ·
    refine ⟨60603088545228708558355709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161608236120609889488948557 60603088545228708558355709)
    ·
      refine ⟨22726158204460765709383391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60603088545228708558355709 22726158204460765709383391)
      ·
        refine ⟨34089237306691148564075087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22726158204460765709383391 34089237306691148564075087)
        ·
          refine ⟨51133855960036722846112631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34089237306691148564075087 51133855960036722846112631)
          ·
            refine ⟨76700783940055084269168947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51133855960036722846112631 76700783940055084269168947)
            ·
              refine ⟨115051175910082626403753421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76700783940055084269168947 115051175910082626403753421)
              ·
                refine ⟨43144190966280984901407533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 115051175910082626403753421 43144190966280984901407533)
                ·
                  refine ⟨16179071612355369338027825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43144190966280984901407533 16179071612355369338027825)
                  ·
                    refine ⟨12134303709266527003520869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16179071612355369338027825 12134303709266527003520869)
                    ·
                      refine ⟨2275181945487473813160163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12134303709266527003520869 2275181945487473813160163)
                      ·
                        rfl

theorem cell23_4430901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_4430901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4430901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4430901 prefixEnd_4430901 := by exact prefixLift 4430901
  have htrace : WordTrace (prefixWord ++ tailWord_4430901) baseStart_4430901 baseEnd_4430901 := by
    simpa [prefixWord, tailWord_4430901, baseEnd_4430901] using wordTrace_append hprefix tailTrace_4430901
  have hstable : (prefixWord ++ tailWord_4430901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4430901).length < 2 ^ (prefixWord ++ tailWord_4430901).sum := by decide
  have hdescent : baseEnd_4430901 < baseStart_4430901 := by decide
  rcases family_descends (prefixWord ++ tailWord_4430901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4430908 : List Nat := [2, 2, 2, 2, 2, 3, 2, 1, 1, 1, 5]
def baseStart_4430908 : Nat := 118140960795 + 4430908 * 2 ^ 59
def prefixEnd_4430908 : Nat := 4983230072969 + 3 ^ 40 * 4430908 * 2
def baseEnd_4430908 : Nat := 2275185539852055285772631

theorem tailTrace_4430908 : CollatzResearch.WordTrace tailWord_4430908 prefixEnd_4430908 2275185539852055285772631 := by
  unfold tailWord_4430908
  simp only [CollatzResearch.WordTrace]
  refine ⟨80804245715792264842226689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107738994287723019789635585 80804245715792264842226689)
  ·
    refine ⟨60603184286844198631670017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80804245715792264842226689 60603184286844198631670017)
    ·
      refine ⟨45452388215133148973752513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60603184286844198631670017 45452388215133148973752513)
      ·
        refine ⟨34089291161349861730314385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45452388215133148973752513 34089291161349861730314385)
        ·
          refine ⟨25566968371012396297735789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34089291161349861730314385 25566968371012396297735789)
          ·
            refine ⟨9587613139129648611650921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25566968371012396297735789 9587613139129648611650921)
            ·
              refine ⟨7190709854347236458738191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9587613139129648611650921 7190709854347236458738191)
              ·
                refine ⟨10786064781520854688107287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7190709854347236458738191 10786064781520854688107287)
                ·
                  refine ⟨16179097172281282032160931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10786064781520854688107287 16179097172281282032160931)
                  ·
                    refine ⟨24268645758421923048241397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16179097172281282032160931 24268645758421923048241397)
                    ·
                      refine ⟨2275185539852055285772631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24268645758421923048241397 2275185539852055285772631)
                      ·
                        rfl

theorem cell23_4430908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_4430908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4430908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4430908 prefixEnd_4430908 := by exact prefixLift 4430908
  have htrace : WordTrace (prefixWord ++ tailWord_4430908) baseStart_4430908 baseEnd_4430908 := by
    simpa [prefixWord, tailWord_4430908, baseEnd_4430908] using wordTrace_append hprefix tailTrace_4430908
  have hstable : (prefixWord ++ tailWord_4430908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4430908).length < 2 ^ (prefixWord ++ tailWord_4430908).sum := by decide
  have hdescent : baseEnd_4430908 < baseStart_4430908 := by decide
  rcases family_descends (prefixWord ++ tailWord_4430908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4430921 : List Nat := [1, 2, 1, 1, 2, 2, 2, 1, 5, 3, 3]
def baseStart_4430921 : Nat := 118140960795 + 4430921 * 2 ^ 59
def prefixEnd_4430921 : Nat := 4983230072969 + 3 ^ 40 * 4430921 * 2
def baseEnd_4430921 : Nat := 2275192215100563734910071

theorem tailTrace_4430921 : CollatzResearch.WordTrace tailWord_4430921 prefixEnd_4430921 2275192215100563734910071 := by
  unfold tailWord_4430921
  simp only [CollatzResearch.WordTrace]
  refine ⟨161608965580537432904676617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107739310387024955269784411 161608965580537432904676617)
  ·
    refine ⟨121206724185403074678507463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161608965580537432904676617 121206724185403074678507463)
    ·
      refine ⟨181810086278104612017761195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121206724185403074678507463 181810086278104612017761195)
      ·
        refine ⟨272715129417156918026641793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181810086278104612017761195 272715129417156918026641793)
        ·
          refine ⟨204536347062867688519981345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 272715129417156918026641793 204536347062867688519981345)
          ·
            refine ⟨153402260297150766389986009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 204536347062867688519981345 153402260297150766389986009)
            ·
              refine ⟨115051695222863074792489507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 153402260297150766389986009 115051695222863074792489507)
              ·
                refine ⟨172577542834294612188734261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115051695222863074792489507 172577542834294612188734261)
                ·
                  refine ⟨16179144640715119892693837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 172577542834294612188734261 16179144640715119892693837)
                  ·
                    refine ⟨6067179240268169959760189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16179144640715119892693837 6067179240268169959760189)
                    ·
                      refine ⟨2275192215100563734910071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6067179240268169959760189 2275192215100563734910071)
                      ·
                        rfl

theorem cell23_4430921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5, 3, 3].length) (baseStart_4430921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4430921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4430921 prefixEnd_4430921 := by exact prefixLift 4430921
  have htrace : WordTrace (prefixWord ++ tailWord_4430921) baseStart_4430921 baseEnd_4430921 := by
    simpa [prefixWord, tailWord_4430921, baseEnd_4430921] using wordTrace_append hprefix tailTrace_4430921
  have hstable : (prefixWord ++ tailWord_4430921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4430921).length < 2 ^ (prefixWord ++ tailWord_4430921).sum := by decide
  have hdescent : baseEnd_4430921 < baseStart_4430921 := by decide
  rcases family_descends (prefixWord ++ tailWord_4430921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4430922 : List Nat := [3, 1, 2, 1, 1, 2, 2, 6, 1, 2, 2]
def baseStart_4430922 : Nat := 118140960795 + 4430922 * 2 ^ 59
def prefixEnd_4430922 : Nat := 4983230072969 + 3 ^ 40 * 4430922 * 2
def baseEnd_4430922 : Nat := 2275192728581218230997567

theorem tailTrace_4430922 : CollatzResearch.WordTrace tailWord_4430922 prefixEnd_4430922 2275192728581218230997567 := by
  unfold tailWord_4430922
  simp only [CollatzResearch.WordTrace]
  refine ⟨40402250513383452518865755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107739334702355873383642013 40402250513383452518865755)
  ·
    refine ⟨60603375770075178778298633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40402250513383452518865755 60603375770075178778298633)
    ·
      refine ⟨45452531827556384083723975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60603375770075178778298633 45452531827556384083723975)
      ·
        refine ⟨68178797741334576125585963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45452531827556384083723975 68178797741334576125585963)
        ·
          refine ⟨102268196612001864188378945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68178797741334576125585963 102268196612001864188378945)
          ·
            refine ⟨76701147459001398141284209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102268196612001864188378945 76701147459001398141284209)
            ·
              refine ⟨57525860594251048605963157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76701147459001398141284209 57525860594251048605963157)
              ·
                refine ⟨2696524715355517903404523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 57525860594251048605963157 2696524715355517903404523)
                ·
                  refine ⟨4044787073033276855106785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2696524715355517903404523 4044787073033276855106785)
                  ·
                    refine ⟨3033590304774957641330089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4044787073033276855106785 3033590304774957641330089)
                    ·
                      refine ⟨2275192728581218230997567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3033590304774957641330089 2275192728581218230997567)
                      ·
                        rfl

theorem cell23_4430922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 6, 1, 2, 2].length) (baseStart_4430922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4430922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4430922 prefixEnd_4430922 := by exact prefixLift 4430922
  have htrace : WordTrace (prefixWord ++ tailWord_4430922) baseStart_4430922 baseEnd_4430922 := by
    simpa [prefixWord, tailWord_4430922, baseEnd_4430922] using wordTrace_append hprefix tailTrace_4430922
  have hstable : (prefixWord ++ tailWord_4430922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4430922).length < 2 ^ (prefixWord ++ tailWord_4430922).sum := by decide
  have hdescent : baseEnd_4430922 < baseStart_4430922 := by decide
  rcases family_descends (prefixWord ++ tailWord_4430922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4430938 : List Nat := [3, 1, 1, 2, 1, 1, 2, 2, 6, 1, 3]
def baseStart_4430938 : Nat := 118140960795 + 4430938 * 2 ^ 59
def prefixEnd_4430938 : Nat := 4983230072969 + 3 ^ 40 * 4430938 * 2
def baseEnd_4430938 : Nat := 2275200944271690168397493

theorem tailTrace_4430938 : CollatzResearch.WordTrace tailWord_4430938 prefixEnd_4430938 2275200944271690168397493 := by
  unfold tailWord_4430938
  simp only [CollatzResearch.WordTrace]
  refine ⟨40402396405368961202011367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107739723747650563205363645 40402396405368961202011367)
  ·
    refine ⟨60603594608053441803017051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40402396405368961202011367 60603594608053441803017051)
    ·
      refine ⟨90905391912080162704525577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60603594608053441803017051 90905391912080162704525577)
      ·
        refine ⟨68179043934060122028394183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90905391912080162704525577 68179043934060122028394183)
        ·
          refine ⟨102268565901090183042591275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68179043934060122028394183 102268565901090183042591275)
          ·
            refine ⟨153402848851635274563886913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102268565901090183042591275 153402848851635274563886913)
            ·
              refine ⟨115052136638726455922915185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 153402848851635274563886913 115052136638726455922915185)
              ·
                refine ⟨86289102479044841942186389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115052136638726455922915185 86289102479044841942186389)
                ·
                  refine ⟨4044801678705226966039987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 86289102479044841942186389 4044801678705226966039987)
                  ·
                    refine ⟨6067202518057840449059981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4044801678705226966039987 6067202518057840449059981)
                    ·
                      refine ⟨2275200944271690168397493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6067202518057840449059981 2275200944271690168397493)
                      ·
                        rfl

theorem cell23_4430938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 6, 1, 3].length) (baseStart_4430938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4430938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4430938 prefixEnd_4430938 := by exact prefixLift 4430938
  have htrace : WordTrace (prefixWord ++ tailWord_4430938) baseStart_4430938 baseEnd_4430938 := by
    simpa [prefixWord, tailWord_4430938, baseEnd_4430938] using wordTrace_append hprefix tailTrace_4430938
  have hstable : (prefixWord ++ tailWord_4430938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4430938).length < 2 ^ (prefixWord ++ tailWord_4430938).sum := by decide
  have hdescent : baseEnd_4430938 < baseStart_4430938 := by decide
  rcases family_descends (prefixWord ++ tailWord_4430938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4431069 : List Nat := [1, 4, 3, 2, 2, 2, 1, 3, 5]
def baseStart_4431069 : Nat := 118140960795 + 4431069 * 2 ^ 59
def prefixEnd_4431069 : Nat := 4983230072969 + 3 ^ 40 * 4431069 * 2
def baseEnd_4431069 : Nat := 252807578915269906206599

theorem tailTrace_4431069 : CollatzResearch.WordTrace tailWord_4431069 prefixEnd_4431069 252807578915269906206599 := by
  unfold tailWord_4431069
  simp only [CollatzResearch.WordTrace]
  refine ⟨161614363584001254181064261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107742909056000836120709507 161614363584001254181064261)
  ·
    refine ⟨30302693172000235158949549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 161614363584001254181064261 30302693172000235158949549)
    ·
      refine ⟨11363509939500088184606081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30302693172000235158949549 11363509939500088184606081)
      ·
        refine ⟨8522632454625066138454561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11363509939500088184606081 8522632454625066138454561)
        ·
          refine ⟨6391974340968799603840921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8522632454625066138454561 6391974340968799603840921)
          ·
            refine ⟨4793980755726599702880691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6391974340968799603840921 4793980755726599702880691)
            ·
              refine ⟨7190971133589899554321037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4793980755726599702880691 7190971133589899554321037)
              ·
                refine ⟨2696614175096212332870389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7190971133589899554321037 2696614175096212332870389)
                ·
                  refine ⟨252807578915269906206599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2696614175096212332870389 252807578915269906206599)
                  ·
                    rfl

theorem cell23_4431069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 3, 5].length) (baseStart_4431069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4431069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4431069 prefixEnd_4431069 := by exact prefixLift 4431069
  have htrace : WordTrace (prefixWord ++ tailWord_4431069) baseStart_4431069 baseEnd_4431069 := by
    simpa [prefixWord, tailWord_4431069, baseEnd_4431069] using wordTrace_append hprefix tailTrace_4431069
  have hstable : (prefixWord ++ tailWord_4431069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4431069).length < 2 ^ (prefixWord ++ tailWord_4431069).sum := by decide
  have hdescent : baseEnd_4431069 < baseStart_4431069 := by decide
  rcases family_descends (prefixWord ++ tailWord_4431069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4431085 : List Nat := [1, 5, 1, 2, 2, 1, 1, 1, 4, 1, 4]
def baseStart_4431085 : Nat := 118140960795 + 4431085 * 2 ^ 59
def prefixEnd_4431085 : Nat := 4983230072969 + 3 ^ 40 * 4431085 * 2
def baseEnd_4431085 : Nat := 2275276425927901093259317

theorem tailTrace_4431085 : CollatzResearch.WordTrace tailWord_4431085 prefixEnd_4431085 2275276425927901093259317 := by
  unfold tailWord_4431085
  simp only [CollatzResearch.WordTrace]
  refine ⟨161614947151943288913646709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107743298101295525942431139 161614947151943288913646709)
  ·
    refine ⟨15151401295494683335654379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 161614947151943288913646709 15151401295494683335654379)
    ·
      refine ⟨22727101943242025003481569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15151401295494683335654379 22727101943242025003481569)
      ·
        refine ⟨17045326457431518752611177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22727101943242025003481569 17045326457431518752611177)
        ·
          refine ⟨12783994843073639064458383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17045326457431518752611177 12783994843073639064458383)
          ·
            refine ⟨19175992264610458596687575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12783994843073639064458383 19175992264610458596687575)
            ·
              refine ⟨28763988396915687895031363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19175992264610458596687575 28763988396915687895031363)
              ·
                refine ⟨43145982595373531842547045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28763988396915687895031363 43145982595373531842547045)
                ·
                  refine ⟨8089871736632537220477571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43145982595373531842547045 8089871736632537220477571)
                  ·
                    refine ⟨12134807604948805830716357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8089871736632537220477571 12134807604948805830716357)
                    ·
                      refine ⟨2275276425927901093259317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12134807604948805830716357 2275276425927901093259317)
                      ·
                        rfl

theorem cell23_4431085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_4431085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4431085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4431085 prefixEnd_4431085 := by exact prefixLift 4431085
  have htrace : WordTrace (prefixWord ++ tailWord_4431085) baseStart_4431085 baseEnd_4431085 := by
    simpa [prefixWord, tailWord_4431085, baseEnd_4431085] using wordTrace_append hprefix tailTrace_4431085
  have hstable : (prefixWord ++ tailWord_4431085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4431085).length < 2 ^ (prefixWord ++ tailWord_4431085).sum := by decide
  have hdescent : baseEnd_4431085 < baseStart_4431085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4431085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4431145 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 8, 3, 2]
def baseStart_4431145 : Nat := 118140960795 + 4431145 * 2 ^ 59
def prefixEnd_4431145 : Nat := 4983230072969 + 3 ^ 40 * 4431145 * 2
def baseEnd_4431145 : Nat := 2275307234767170858509041

theorem tailTrace_4431145 : CollatzResearch.WordTrace tailWord_4431145 prefixEnd_4431145 2275307234767170858509041 := by
  unfold tailWord_4431145
  simp only [CollatzResearch.WordTrace]
  refine ⟨161617135531725919160830889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107744757021150612773887259 161617135531725919160830889)
  ·
    refine ⟨121212851648794439370623167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161617135531725919160830889 121212851648794439370623167)
    ·
      refine ⟨181819277473191659055934751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121212851648794439370623167 181819277473191659055934751)
      ·
        refine ⟨272728916209787488583902127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181819277473191659055934751 272728916209787488583902127)
        ·
          refine ⟨409093374314681232875853191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272728916209787488583902127 409093374314681232875853191)
          ·
            refine ⟨613640061472021849313779787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 409093374314681232875853191 613640061472021849313779787)
            ·
              refine ⟨920460092208032773970669681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 613640061472021849313779787 920460092208032773970669681)
              ·
                refine ⟨690345069156024580478002261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 920460092208032773970669681 690345069156024580478002261)
                ·
                  refine ⟨8089981279172163052476589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 690345069156024580478002261 8089981279172163052476589)
                  ·
                    refine ⟨3033742979689561144678721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8089981279172163052476589 3033742979689561144678721)
                    ·
                      refine ⟨2275307234767170858509041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3033742979689561144678721 2275307234767170858509041)
                      ·
                        rfl

theorem cell23_4431145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 8, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 8, 3, 2].length) (baseStart_4431145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4431145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4431145 prefixEnd_4431145 := by exact prefixLift 4431145
  have htrace : WordTrace (prefixWord ++ tailWord_4431145) baseStart_4431145 baseEnd_4431145 := by
    simpa [prefixWord, tailWord_4431145, baseEnd_4431145] using wordTrace_append hprefix tailTrace_4431145
  have hstable : (prefixWord ++ tailWord_4431145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4431145).length < 2 ^ (prefixWord ++ tailWord_4431145).sum := by decide
  have hdescent : baseEnd_4431145 < baseStart_4431145 := by decide
  rcases family_descends (prefixWord ++ tailWord_4431145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4431146 : List Nat := [3, 1, 4, 2, 1, 1, 4, 2, 1, 4]
def baseStart_4431146 : Nat := 118140960795 + 4431146 * 2 ^ 59
def prefixEnd_4431146 : Nat := 4983230072969 + 3 ^ 40 * 4431146 * 2
def baseEnd_4431146 : Nat := 758435916082608451532179

theorem tailTrace_4431146 : CollatzResearch.WordTrace tailWord_4431146 prefixEnd_4431146 758435916082608451532179 := by
  unfold tailWord_4431146
  simp only [CollatzResearch.WordTrace]
  refine ⟨40404293001180574082904323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107744781336481530887744861 40404293001180574082904323)
  ·
    refine ⟨60606439501770861124356485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40404293001180574082904323 60606439501770861124356485)
    ·
      refine ⟨11363707406582036460816841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60606439501770861124356485 11363707406582036460816841)
      ·
        refine ⟨8522780554936527345612631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11363707406582036460816841 8522780554936527345612631)
        ·
          refine ⟨12784170832404791018418947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8522780554936527345612631 12784170832404791018418947)
          ·
            refine ⟨19176256248607186527628421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12784170832404791018418947 19176256248607186527628421)
            ·
              refine ⟨3595548046613847473930329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19176256248607186527628421 3595548046613847473930329)
              ·
                refine ⟨2696661034960385605447747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3595548046613847473930329 2696661034960385605447747)
                ·
                  refine ⟨4044991552440578408171621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2696661034960385605447747 4044991552440578408171621)
                  ·
                    refine ⟨758435916082608451532179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4044991552440578408171621 758435916082608451532179)
                    ·
                      rfl

theorem cell23_4431146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_4431146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4431146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4431146 prefixEnd_4431146 := by exact prefixLift 4431146
  have htrace : WordTrace (prefixWord ++ tailWord_4431146) baseStart_4431146 baseEnd_4431146 := by
    simpa [prefixWord, tailWord_4431146, baseEnd_4431146] using wordTrace_append hprefix tailTrace_4431146
  have hstable : (prefixWord ++ tailWord_4431146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4431146).length < 2 ^ (prefixWord ++ tailWord_4431146).sum := by decide
  have hdescent : baseEnd_4431146 < baseStart_4431146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4431146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4431169 : List Nat := [1, 2, 5, 2, 1, 2, 1, 2, 3, 1, 3]
def baseStart_4431169 : Nat := 118140960795 + 4431169 * 2 ^ 59
def prefixEnd_4431169 : Nat := 4983230072969 + 3 ^ 40 * 4431169 * 2
def baseEnd_4431169 : Nat := 2275319558302878764608931

theorem tailTrace_4431169 : CollatzResearch.WordTrace tailWord_4431169 prefixEnd_4431169 2275319558302878764608931 := by
  unfold tailWord_4431169
  simp only [CollatzResearch.WordTrace]
  refine ⟨161618010883638971259704561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107745340589092647506469707 161618010883638971259704561)
  ·
    refine ⟨121213508162729228444778421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161618010883638971259704561 121213508162729228444778421)
    ·
      refine ⟨11363766390255865166697977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 121213508162729228444778421 11363766390255865166697977)
      ·
        refine ⟨8522824792691898875023483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11363766390255865166697977 8522824792691898875023483)
        ·
          refine ⟨12784237189037848312535225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8522824792691898875023483 12784237189037848312535225)
          ·
            refine ⟨9588177891778386234401419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12784237189037848312535225 9588177891778386234401419)
            ·
              refine ⟨14382266837667579351602129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9588177891778386234401419 14382266837667579351602129)
              ·
                refine ⟨10786700128250684513701597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14382266837667579351602129 10786700128250684513701597)
                ·
                  refine ⟨4045012548094006692638099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10786700128250684513701597 4045012548094006692638099)
                  ·
                    refine ⟨6067518822141010038957149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4045012548094006692638099 6067518822141010038957149)
                    ·
                      refine ⟨2275319558302878764608931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6067518822141010038957149 2275319558302878764608931)
                      ·
                        rfl

theorem cell23_4431169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_4431169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4431169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4431169 prefixEnd_4431169 := by exact prefixLift 4431169
  have htrace : WordTrace (prefixWord ++ tailWord_4431169) baseStart_4431169 baseEnd_4431169 := by
    simpa [prefixWord, tailWord_4431169, baseEnd_4431169] using wordTrace_append hprefix tailTrace_4431169
  have hstable : (prefixWord ++ tailWord_4431169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4431169).length < 2 ^ (prefixWord ++ tailWord_4431169).sum := by decide
  have hdescent : baseEnd_4431169 < baseStart_4431169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4431169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4431172 : List Nat := [2, 3, 4, 1, 1, 1, 2, 1, 3, 5]
def baseStart_4431172 : Nat := 118140960795 + 4431172 * 2 ^ 59
def prefixEnd_4431172 : Nat := 4983230072969 + 3 ^ 40 * 4431172 * 2
def baseEnd_4431172 : Nat := 758440366248280750957139

theorem tailTrace_4431172 : CollatzResearch.WordTrace tailWord_4431172 prefixEnd_4431172 758440366248280750957139 := by
  unfold tailWord_4431172
  simp only [CollatzResearch.WordTrace]
  refine ⟨80809060151314051386031885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107745413535085401848042513 80809060151314051386031885)
  ·
    refine ⟨30303397556742769269761957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80809060151314051386031885 30303397556742769269761957)
    ·
      refine ⟨5681887041889269238080367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30303397556742769269761957 5681887041889269238080367)
      ·
        refine ⟨8522830562833903857120551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5681887041889269238080367 8522830562833903857120551)
        ·
          refine ⟨12784245844250855785680827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8522830562833903857120551 12784245844250855785680827)
          ·
            refine ⟨19176368766376283678521241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12784245844250855785680827 19176368766376283678521241)
            ·
              refine ⟨14382276574782212758890931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19176368766376283678521241 14382276574782212758890931)
              ·
                refine ⟨21573414862173319138336397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14382276574782212758890931 21573414862173319138336397)
                ·
                  refine ⟨8090030573314994676876149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21573414862173319138336397 8090030573314994676876149)
                  ·
                    refine ⟨758440366248280750957139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8090030573314994676876149 758440366248280750957139)
                    ·
                      rfl

theorem cell23_4431172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_4431172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4431172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4431172 prefixEnd_4431172 := by exact prefixLift 4431172
  have htrace : WordTrace (prefixWord ++ tailWord_4431172) baseStart_4431172 baseEnd_4431172 := by
    simpa [prefixWord, tailWord_4431172, baseEnd_4431172] using wordTrace_append hprefix tailTrace_4431172
  have hstable : (prefixWord ++ tailWord_4431172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4431172).length < 2 ^ (prefixWord ++ tailWord_4431172).sum := by decide
  have hdescent : baseEnd_4431172 < baseStart_4431172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4431172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4431175 : List Nat := [1, 1, 4, 1, 2, 3, 2, 1, 3, 1, 4]
def baseStart_4431175 : Nat := 118140960795 + 4431175 * 2 ^ 59
def prefixEnd_4431175 : Nat := 4983230072969 + 3 ^ 40 * 4431175 * 2
def baseEnd_4431175 : Nat := 2275322639186805741133903

theorem tailTrace_4431175 : CollatzResearch.WordTrace tailWord_4431175 prefixEnd_4431175 2275322639186805741133903 := by
  unfold tailWord_4431175
  simp only [CollatzResearch.WordTrace]
  refine ⟨161618229721617234284422979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107745486481078156189615319 161618229721617234284422979)
  ·
    refine ⟨242427344582425851426634469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161618229721617234284422979 242427344582425851426634469)
    ·
      refine ⟨45455127109204847142493963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 242427344582425851426634469 45455127109204847142493963)
      ·
        refine ⟨68182690663807270713740945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45455127109204847142493963 68182690663807270713740945)
        ·
          refine ⟨51137017997855453035305709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68182690663807270713740945 51137017997855453035305709)
          ·
            refine ⟨19176381749195794888239641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51137017997855453035305709 19176381749195794888239641)
            ·
              refine ⟨14382286311896846166179731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19176381749195794888239641 14382286311896846166179731)
              ·
                refine ⟨21573429467845269249269597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14382286311896846166179731 21573429467845269249269597)
                ·
                  refine ⟨8090036050441975968476099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21573429467845269249269597 8090036050441975968476099)
                  ·
                    refine ⟨12135054075662963952714149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8090036050441975968476099 12135054075662963952714149)
                    ·
                      refine ⟨2275322639186805741133903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12135054075662963952714149 2275322639186805741133903)
                      ·
                        rfl

theorem cell23_4431175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 3, 1, 4].length) (baseStart_4431175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4431175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4431175 prefixEnd_4431175 := by exact prefixLift 4431175
  have htrace : WordTrace (prefixWord ++ tailWord_4431175) baseStart_4431175 baseEnd_4431175 := by
    simpa [prefixWord, tailWord_4431175, baseEnd_4431175] using wordTrace_append hprefix tailTrace_4431175
  have hstable : (prefixWord ++ tailWord_4431175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4431175).length < 2 ^ (prefixWord ++ tailWord_4431175).sum := by decide
  have hdescent : baseEnd_4431175 < baseStart_4431175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4431175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4431185 : List Nat := [1, 2, 2, 1, 4, 1, 2, 2, 4, 4]
def baseStart_4431185 : Nat := 118140960795 + 4431185 * 2 ^ 59
def prefixEnd_4431185 : Nat := 4983230072969 + 3 ^ 40 * 4431185 * 2
def baseEnd_4431185 : Nat := 758442591331116900669619

theorem tailTrace_4431185 : CollatzResearch.WordTrace tailWord_4431185 prefixEnd_4431185 758442591331116900669619 := by
  unfold tailWord_4431185
  simp only [CollatzResearch.WordTrace]
  refine ⟨161618594451581005992287009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107745729634387337328191339 161618594451581005992287009)
  ·
    refine ⟨121213945838685754494215257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161618594451581005992287009 121213945838685754494215257)
    ·
      refine ⟨90910459379014315870661443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121213945838685754494215257 90910459379014315870661443)
      ·
        refine ⟨136365689068521473805992165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90910459379014315870661443 136365689068521473805992165)
        ·
          refine ⟨25568566700347776338623531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 136365689068521473805992165 25568566700347776338623531)
          ·
            refine ⟨38352850050521664507935297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25568566700347776338623531 38352850050521664507935297)
            ·
              refine ⟨28764637537891248380951473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38352850050521664507935297 28764637537891248380951473)
              ·
                refine ⟨21573478153418436285713605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28764637537891248380951473 21573478153418436285713605)
                ·
                  refine ⟨4045027153765956803571301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21573478153418436285713605 4045027153765956803571301)
                  ·
                    refine ⟨758442591331116900669619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4045027153765956803571301 758442591331116900669619)
                    ·
                      rfl

theorem cell23_4431185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 4, 4].length) (baseStart_4431185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4431185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4431185 prefixEnd_4431185 := by exact prefixLift 4431185
  have htrace : WordTrace (prefixWord ++ tailWord_4431185) baseStart_4431185 baseEnd_4431185 := by
    simpa [prefixWord, tailWord_4431185, baseEnd_4431185] using wordTrace_append hprefix tailTrace_4431185
  have hstable : (prefixWord ++ tailWord_4431185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4431185).length < 2 ^ (prefixWord ++ tailWord_4431185).sum := by decide
  have hdescent : baseEnd_4431185 < baseStart_4431185 := by decide
  rcases family_descends (prefixWord ++ tailWord_4431185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4431189 : List Nat := [1, 3, 2, 2, 3, 3, 2, 1, 1, 5]
def baseStart_4431189 : Nat := 118140960795 + 4431189 * 2 ^ 59
def prefixEnd_4431189 : Nat := 4983230072969 + 3 ^ 40 * 4431189 * 2
def baseEnd_4431189 : Nat := 758443275971989562119613

theorem tailTrace_4431189 : CollatzResearch.WordTrace tailWord_4431189 prefixEnd_4431189 758443275971989562119613 := by
  unfold tailWord_4431189
  simp only [CollatzResearch.WordTrace]
  refine ⟨161618740343566514675432621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107745826895711009783621747 161618740343566514675432621)
  ·
    refine ⟨60607027628837443003287233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161618740343566514675432621 60607027628837443003287233)
    ·
      refine ⟨45455270721628082252465425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60607027628837443003287233 45455270721628082252465425)
      ·
        refine ⟨34091453041221061689349069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45455270721628082252465425 34091453041221061689349069)
        ·
          refine ⟨12784294890457898133505901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34091453041221061689349069 12784294890457898133505901)
          ·
            refine ⟨4794110583921711800064713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12784294890457898133505901 4794110583921711800064713)
            ·
              refine ⟨3595582937941283850048535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4794110583921711800064713 3595582937941283850048535)
              ·
                refine ⟨5393374406911925775072803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3595582937941283850048535 5393374406911925775072803)
                ·
                  refine ⟨8090061610367888662609205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5393374406911925775072803 8090061610367888662609205)
                  ·
                    refine ⟨758443275971989562119613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8090061610367888662609205 758443275971989562119613)
                    ·
                      rfl

theorem cell23_4431189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2, 1, 1, 5].length) (baseStart_4431189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4431189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4431189 prefixEnd_4431189 := by exact prefixLift 4431189
  have htrace : WordTrace (prefixWord ++ tailWord_4431189) baseStart_4431189 baseEnd_4431189 := by
    simpa [prefixWord, tailWord_4431189, baseEnd_4431189] using wordTrace_append hprefix tailTrace_4431189
  have hstable : (prefixWord ++ tailWord_4431189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4431189).length < 2 ^ (prefixWord ++ tailWord_4431189).sum := by decide
  have hdescent : baseEnd_4431189 < baseStart_4431189 := by decide
  rcases family_descends (prefixWord ++ tailWord_4431189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4431192 : List Nat := [2, 1, 2, 2, 1, 1, 3, 2, 5, 2, 2]
def baseStart_4431192 : Nat := 118140960795 + 4431192 * 2 ^ 59
def prefixEnd_4431192 : Nat := 4983230072969 + 3 ^ 40 * 4431192 * 2
def baseEnd_4431192 : Nat := 2275331368357932174621325

theorem tailTrace_4431192 : CollatzResearch.WordTrace tailWord_4431192 prefixEnd_4431192 2275331368357932174621325 := by
  unfold tailWord_4431192
  simp only [CollatzResearch.WordTrace]
  refine ⟨80809424881277823093895915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107745899841703764125194553 80809424881277823093895915)
  ·
    refine ⟨121214137321916734640843873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80809424881277823093895915 121214137321916734640843873)
    ·
      refine ⟨90910602991437550980632905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121214137321916734640843873 90910602991437550980632905)
      ·
        refine ⟨68182952243578163235474679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90910602991437550980632905 68182952243578163235474679)
        ·
          refine ⟨102274428365367244853212019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68182952243578163235474679 102274428365367244853212019)
          ·
            refine ⟨153411642548050867279818029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102274428365367244853212019 153411642548050867279818029)
            ·
              refine ⟨57529365955519075229931761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 153411642548050867279818029 57529365955519075229931761)
              ·
                refine ⟨43147024466639306422448821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57529365955519075229931761 43147024466639306422448821)
                ·
                  refine ⟨4045033543747434977104577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43147024466639306422448821 4045033543747434977104577)
                  ·
                    refine ⟨3033775157810576232828433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4045033543747434977104577 3033775157810576232828433)
                    ·
                      refine ⟨2275331368357932174621325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3033775157810576232828433 2275331368357932174621325)
                      ·
                        rfl

theorem cell23_4431192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 5, 2, 2].length) (baseStart_4431192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4431192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4431192 prefixEnd_4431192 := by exact prefixLift 4431192
  have htrace : WordTrace (prefixWord ++ tailWord_4431192) baseStart_4431192 baseEnd_4431192 := by
    simpa [prefixWord, tailWord_4431192, baseEnd_4431192] using wordTrace_append hprefix tailTrace_4431192
  have hstable : (prefixWord ++ tailWord_4431192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4431192).length < 2 ^ (prefixWord ++ tailWord_4431192).sum := by decide
  have hdescent : baseEnd_4431192 < baseStart_4431192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4431192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4431202 : List Nat := [3, 3, 2, 1, 1, 1, 3, 1, 4, 4]
def baseStart_4431202 : Nat := 118140960795 + 4431202 * 2 ^ 59
def prefixEnd_4431202 : Nat := 4983230072969 + 3 ^ 40 * 4431202 * 2
def baseEnd_4431202 : Nat := 758445501054825711832093

theorem tailTrace_4431202 : CollatzResearch.WordTrace tailWord_4431202 prefixEnd_4431202 758445501054825711832093 := by
  unfold tailWord_4431202
  simp only [CollatzResearch.WordTrace]
  refine ⟨40404803623129854473913965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107746142995012945263770573 40404803623129854473913965)
  ·
    refine ⟨15151801358673695427717737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40404803623129854473913965 15151801358673695427717737)
    ·
      refine ⟨11363851019005271570788303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15151801358673695427717737 11363851019005271570788303)
      ·
        refine ⟨17045776528507907356182455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11363851019005271570788303 17045776528507907356182455)
        ·
          refine ⟨25568664792761861034273683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17045776528507907356182455 25568664792761861034273683)
          ·
            refine ⟨38352997189142791551410525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25568664792761861034273683 38352997189142791551410525)
            ·
              refine ⟨14382373945928546831778947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38352997189142791551410525 14382373945928546831778947)
              ·
                refine ⟨21573560918892820247668421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14382373945928546831778947 21573560918892820247668421)
                ·
                  refine ⟨4045042672292403796437829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21573560918892820247668421 4045042672292403796437829)
                  ·
                    refine ⟨758445501054825711832093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4045042672292403796437829 758445501054825711832093)
                    ·
                      rfl

theorem cell23_4431202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_4431202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4431202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4431202 prefixEnd_4431202 := by exact prefixLift 4431202
  have htrace : WordTrace (prefixWord ++ tailWord_4431202) baseStart_4431202 baseEnd_4431202 := by
    simpa [prefixWord, tailWord_4431202, baseEnd_4431202] using wordTrace_append hprefix tailTrace_4431202
  have hstable : (prefixWord ++ tailWord_4431202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4431202).length < 2 ^ (prefixWord ++ tailWord_4431202).sum := by decide
  have hdescent : baseEnd_4431202 < baseStart_4431202 := by decide
  rcases family_descends (prefixWord ++ tailWord_4431202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4431260 : List Nat := [2, 2, 3, 4, 2, 1, 1, 1, 3, 2, 2]
def baseStart_4431260 : Nat := 118140960795 + 4431260 * 2 ^ 59
def prefixEnd_4431260 : Nat := 4983230072969 + 3 ^ 40 * 4431260 * 2
def baseEnd_4431260 : Nat := 2275366285042437908571013

theorem tailTrace_4431260 : CollatzResearch.WordTrace tailWord_4431260 prefixEnd_4431260 2275366285042437908571013 := by
  unfold tailWord_4431260
  simp only [CollatzResearch.WordTrace]
  refine ⟨80810664963154646900633617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107747553284206195867511489 80810664963154646900633617)
  ·
    refine ⟨60607998722365985175475213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80810664963154646900633617 60607998722365985175475213)
    ·
      refine ⟨22727999520887244440803205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60607998722365985175475213 22727999520887244440803205)
      ·
        refine ⟨4261499910166358332650601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22727999520887244440803205 4261499910166358332650601)
        ·
          refine ⟨3196124932624768749487951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4261499910166358332650601 3196124932624768749487951)
          ·
            refine ⟨4794187398937153124231927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3196124932624768749487951 4794187398937153124231927)
            ·
              refine ⟨7191281098405729686347891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4794187398937153124231927 7191281098405729686347891)
              ·
                refine ⟨10786921647608594529521837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7191281098405729686347891 10786921647608594529521837)
                ·
                  refine ⟨4045095617853222948570689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10786921647608594529521837 4045095617853222948570689)
                  ·
                    refine ⟨3033821713389917211428017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4045095617853222948570689 3033821713389917211428017)
                    ·
                      refine ⟨2275366285042437908571013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3033821713389917211428017 2275366285042437908571013)
                      ·
                        rfl

theorem cell23_4431260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_4431260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4431260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4431260 prefixEnd_4431260 := by exact prefixLift 4431260
  have htrace : WordTrace (prefixWord ++ tailWord_4431260) baseStart_4431260 baseEnd_4431260 := by
    simpa [prefixWord, tailWord_4431260, baseEnd_4431260] using wordTrace_append hprefix tailTrace_4431260
  have hstable : (prefixWord ++ tailWord_4431260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4431260).length < 2 ^ (prefixWord ++ tailWord_4431260).sum := by decide
  have hdescent : baseEnd_4431260 < baseStart_4431260 := by decide
  rcases family_descends (prefixWord ++ tailWord_4431260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4431352 : List Nat := [2, 1, 2, 1, 1, 5, 3, 1, 2, 5]
def baseStart_4431352 : Nat := 118140960795 + 4431352 * 2 ^ 59
def prefixEnd_4431352 : Nat := 4983230072969 + 3 ^ 40 * 4431352 * 2
def baseEnd_4431352 : Nat := 758471175087550516206863

theorem tailTrace_4431352 : CollatzResearch.WordTrace tailWord_4431352 prefixEnd_4431352 758471175087550516206863 := by
  unfold tailWord_4431352
  simp only [CollatzResearch.WordTrace]
  refine ⟨80812342720987996756808155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107749790294650662342410873 80812342720987996756808155)
  ·
    refine ⟨121218514081481995135212233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80812342720987996756808155 121218514081481995135212233)
    ·
      refine ⟨90913885561111496351409175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121218514081481995135212233 90913885561111496351409175)
      ·
        refine ⟨136370828341667244527113763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90913885561111496351409175 136370828341667244527113763)
        ·
          refine ⟨204556242512500866790670645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136370828341667244527113763 204556242512500866790670645)
          ·
            refine ⟨19177147735546956261625373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 204556242512500866790670645 19177147735546956261625373)
            ·
              refine ⟨7191430400830108598109515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19177147735546956261625373 7191430400830108598109515)
              ·
                refine ⟨10787145601245162897164273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7191430400830108598109515 10787145601245162897164273)
                ·
                  refine ⟨8090359200933872172873205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10787145601245162897164273 8090359200933872172873205)
                  ·
                    refine ⟨758471175087550516206863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8090359200933872172873205 758471175087550516206863)
                    ·
                      rfl

theorem cell23_4431352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 1, 2, 5].length) (baseStart_4431352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4431352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4431352 prefixEnd_4431352 := by exact prefixLift 4431352
  have htrace : WordTrace (prefixWord ++ tailWord_4431352) baseStart_4431352 baseEnd_4431352 := by
    simpa [prefixWord, tailWord_4431352, baseEnd_4431352] using wordTrace_append hprefix tailTrace_4431352
  have hstable : (prefixWord ++ tailWord_4431352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4431352).length < 2 ^ (prefixWord ++ tailWord_4431352).sum := by decide
  have hdescent : baseEnd_4431352 < baseStart_4431352 := by decide
  rcases family_descends (prefixWord ++ tailWord_4431352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4431355 : List Nat := [1, 1, 1, 1, 1, 3, 2, 5, 1, 3, 4]
def baseStart_4431355 : Nat := 118140960795 + 4431355 * 2 ^ 59
def prefixEnd_4431355 : Nat := 4983230072969 + 3 ^ 40 * 4431355 * 2
def baseEnd_4431355 : Nat := 2275415065704615036883075

theorem tailTrace_4431355 : CollatzResearch.WordTrace tailWord_4431355 prefixEnd_4431355 2275415065704615036883075 := by
  unfold tailWord_4431355
  simp only [CollatzResearch.WordTrace]
  refine ⟨161624794860965125025975519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107749863240643416683983679 161624794860965125025975519)
  ·
    refine ⟨242437192291447687538963279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161624794860965125025975519 242437192291447687538963279)
    ·
      refine ⟨363655788437171531308444919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242437192291447687538963279 363655788437171531308444919)
      ·
        refine ⟨545483682655757296962667379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 363655788437171531308444919 545483682655757296962667379)
        ·
          refine ⟨818225523983635945444001069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 545483682655757296962667379 818225523983635945444001069)
          ·
            refine ⟨306834571493863479541500401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 818225523983635945444001069 306834571493863479541500401)
            ·
              refine ⟨230125928620397609656125301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 306834571493863479541500401 230125928620397609656125301)
              ·
                refine ⟨21574305808162275905261747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 230125928620397609656125301 21574305808162275905261747)
                ·
                  refine ⟨32361458712243413857892621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21574305808162275905261747 32361458712243413857892621)
                  ·
                    refine ⟨12135547017091280196709733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32361458712243413857892621 12135547017091280196709733)
                    ·
                      refine ⟨2275415065704615036883075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12135547017091280196709733 2275415065704615036883075)
                      ·
                        rfl

theorem cell23_4431355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 3, 4].length) (baseStart_4431355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4431355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4431355 prefixEnd_4431355 := by exact prefixLift 4431355
  have htrace : WordTrace (prefixWord ++ tailWord_4431355) baseStart_4431355 baseEnd_4431355 := by
    simpa [prefixWord, tailWord_4431355, baseEnd_4431355] using wordTrace_append hprefix tailTrace_4431355
  have hstable : (prefixWord ++ tailWord_4431355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4431355).length < 2 ^ (prefixWord ++ tailWord_4431355).sum := by decide
  have hdescent : baseEnd_4431355 < baseStart_4431355 := by decide
  rcases family_descends (prefixWord ++ tailWord_4431355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4431385 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 4, 4, 4]
def baseStart_4431385 : Nat := 118140960795 + 4431385 * 2 ^ 59
def prefixEnd_4431385 : Nat := 4983230072969 + 3 ^ 40 * 4431385 * 2
def baseEnd_4431385 : Nat := 2275430470124249919507937

theorem tailTrace_4431385 : CollatzResearch.WordTrace tailWord_4431385 prefixEnd_4431385 2275430470124249919507937 := by
  unfold tailWord_4431385
  simp only [CollatzResearch.WordTrace]
  refine ⟨161625889050856440149567609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107750592700570960099711739 161625889050856440149567609)
  ·
    refine ⟨121219416788142330112175707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161625889050856440149567609 121219416788142330112175707)
    ·
      refine ⟨181829125182213495168263561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121219416788142330112175707 181829125182213495168263561)
      ·
        refine ⟨136371843886660121376197671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181829125182213495168263561 136371843886660121376197671)
        ·
          refine ⟨204557765829990182064296507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136371843886660121376197671 204557765829990182064296507)
          ·
            refine ⟨306836648744985273096444761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204557765829990182064296507 306836648744985273096444761)
            ·
              refine ⟨230127486558738954822333571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 306836648744985273096444761 230127486558738954822333571)
              ·
                refine ⟨345191229838108432233500357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 230127486558738954822333571 345191229838108432233500357)
                ·
                  refine ⟨64723355594645331043781317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 345191229838108432233500357 64723355594645331043781317)
                  ·
                    refine ⟨12135629173995999570708997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 64723355594645331043781317 12135629173995999570708997)
                    ·
                      refine ⟨2275430470124249919507937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12135629173995999570708997 2275430470124249919507937)
                      ·
                        rfl

theorem cell23_4431385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 4, 4].length) (baseStart_4431385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4431385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4431385 prefixEnd_4431385 := by exact prefixLift 4431385
  have htrace : WordTrace (prefixWord ++ tailWord_4431385) baseStart_4431385 baseEnd_4431385 := by
    simpa [prefixWord, tailWord_4431385, baseEnd_4431385] using wordTrace_append hprefix tailTrace_4431385
  have hstable : (prefixWord ++ tailWord_4431385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4431385).length < 2 ^ (prefixWord ++ tailWord_4431385).sum := by decide
  have hdescent : baseEnd_4431385 < baseStart_4431385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4431385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4431389 : List Nat := [1, 4, 2, 2, 1, 1, 1, 3, 2, 4, 2]
def baseStart_4431389 : Nat := 118140960795 + 4431389 * 2 ^ 59
def prefixEnd_4431389 : Nat := 4983230072969 + 3 ^ 40 * 4431389 * 2
def baseEnd_4431389 : Nat := 2275432524046867903857919

theorem tailTrace_4431389 : CollatzResearch.WordTrace tailWord_4431389 prefixEnd_4431389 2275432524046867903857919 := by
  unfold tailWord_4431389
  simp only [CollatzResearch.WordTrace]
  refine ⟨161626034942841948832713221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107750689961894632555142147 161626034942841948832713221)
  ·
    refine ⟨30304881551782865406133729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 161626034942841948832713221 30304881551782865406133729)
    ·
      refine ⟨22728661163837149054600297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30304881551782865406133729 22728661163837149054600297)
      ·
        refine ⟨17046495872877861790950223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22728661163837149054600297 17046495872877861790950223)
        ·
          refine ⟨25569743809316792686425335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17046495872877861790950223 25569743809316792686425335)
          ·
            refine ⟨38354615713975189029638003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25569743809316792686425335 38354615713975189029638003)
            ·
              refine ⟨57531923570962783544457005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38354615713975189029638003 57531923570962783544457005)
              ·
                refine ⟨21574471339111043829171377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57531923570962783544457005 21574471339111043829171377)
                ·
                  refine ⟨16180853504333282871878533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21574471339111043829171377 16180853504333282871878533)
                  ·
                    refine ⟨3033910032062490538477225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16180853504333282871878533 3033910032062490538477225)
                    ·
                      refine ⟨2275432524046867903857919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3033910032062490538477225 2275432524046867903857919)
                      ·
                        rfl

theorem cell23_4431389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_4431389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4431389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4431389 prefixEnd_4431389 := by exact prefixLift 4431389
  have htrace : WordTrace (prefixWord ++ tailWord_4431389) baseStart_4431389 baseEnd_4431389 := by
    simpa [prefixWord, tailWord_4431389, baseEnd_4431389] using wordTrace_append hprefix tailTrace_4431389
  have hstable : (prefixWord ++ tailWord_4431389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4431389).length < 2 ^ (prefixWord ++ tailWord_4431389).sum := by decide
  have hdescent : baseEnd_4431389 < baseStart_4431389 := by decide
  rcases family_descends (prefixWord ++ tailWord_4431389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4431402 : List Nat := [3, 1, 4, 1, 1, 1, 1, 1, 2, 4, 4]
def baseStart_4431402 : Nat := 118140960795 + 4431402 * 2 ^ 59
def prefixEnd_4431402 : Nat := 4983230072969 + 3 ^ 40 * 4431402 * 2
def baseEnd_4431402 : Nat := 2275439199295376352995359

theorem tailTrace_4431402 : CollatzResearch.WordTrace tailWord_4431402 prefixEnd_4431402 2275439199295376352995359 := by
  unfold tailWord_4431402
  simp only [CollatzResearch.WordTrace]
  refine ⟨40406627272948713013234115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107751006061196568035290973 40406627272948713013234115)
  ·
    refine ⟨60609940909423069519851173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40406627272948713013234115 60609940909423069519851173)
    ·
      refine ⟨11364363920516825534972095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60609940909423069519851173 11364363920516825534972095)
      ·
        refine ⟨17046545880775238302458143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11364363920516825534972095 17046545880775238302458143)
        ·
          refine ⟨25569818821162857453687215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17046545880775238302458143 25569818821162857453687215)
          ·
            refine ⟨38354728231744286180530823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25569818821162857453687215 38354728231744286180530823)
            ·
              refine ⟨57532092347616429270796235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38354728231744286180530823 57532092347616429270796235)
              ·
                refine ⟨86298138521424643906194353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57532092347616429270796235 86298138521424643906194353)
                ·
                  refine ⟨64723603891068482929645765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86298138521424643906194353 64723603891068482929645765)
                  ·
                    refine ⟨12135675729575340549308581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 64723603891068482929645765 12135675729575340549308581)
                    ·
                      refine ⟨2275439199295376352995359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12135675729575340549308581 2275439199295376352995359)
                      ·
                        rfl

theorem cell23_4431402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_4431402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4431402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4431402 prefixEnd_4431402 := by exact prefixLift 4431402
  have htrace : WordTrace (prefixWord ++ tailWord_4431402) baseStart_4431402 baseEnd_4431402 := by
    simpa [prefixWord, tailWord_4431402, baseEnd_4431402] using wordTrace_append hprefix tailTrace_4431402
  have hstable : (prefixWord ++ tailWord_4431402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4431402).length < 2 ^ (prefixWord ++ tailWord_4431402).sum := by decide
  have hdescent : baseEnd_4431402 < baseStart_4431402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4431402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4431416 : List Nat := [2, 1, 2, 1, 4, 2, 3, 3, 1, 4]
def baseStart_4431416 : Nat := 118140960795 + 4431416 * 2 ^ 59
def prefixEnd_4431416 : Nat := 4983230072969 + 3 ^ 40 * 4431416 * 2
def baseEnd_4431416 : Nat := 758482129341513099406765

theorem tailTrace_4431416 : CollatzResearch.WordTrace tailWord_4431416 prefixEnd_4431416 758482129341513099406765 := by
  unfold tailWord_4431416
  simp only [CollatzResearch.WordTrace]
  refine ⟨80813509856872066221973051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107751346475829421629297401 80813509856872066221973051)
  ·
    refine ⟨121220264785308099332959577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80813509856872066221973051 121220264785308099332959577)
    ·
      refine ⟨90915198588981074499719683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121220264785308099332959577 90915198588981074499719683)
      ·
        refine ⟨136372797883471611749579525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90915198588981074499719683 136372797883471611749579525)
        ·
          refine ⟨25569899603150927203046161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 136372797883471611749579525 25569899603150927203046161)
          ·
            refine ⟨19177424702363195402284621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25569899603150927203046161 19177424702363195402284621)
            ·
              refine ⟨7191534263386198275856733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19177424702363195402284621 7191534263386198275856733)
              ·
                refine ⟨2696825348769824353446275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7191534263386198275856733 2696825348769824353446275)
                ·
                  refine ⟨4045238023154736530169413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2696825348769824353446275 4045238023154736530169413)
                  ·
                    refine ⟨758482129341513099406765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4045238023154736530169413 758482129341513099406765)
                    ·
                      rfl

theorem cell23_4431416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 3, 1, 4].length) (baseStart_4431416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4431416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4431416 prefixEnd_4431416 := by exact prefixLift 4431416
  have htrace : WordTrace (prefixWord ++ tailWord_4431416) baseStart_4431416 baseEnd_4431416 := by
    simpa [prefixWord, tailWord_4431416, baseEnd_4431416] using wordTrace_append hprefix tailTrace_4431416
  have hstable : (prefixWord ++ tailWord_4431416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4431416).length < 2 ^ (prefixWord ++ tailWord_4431416).sum := by decide
  have hdescent : baseEnd_4431416 < baseStart_4431416 := by decide
  rcases family_descends (prefixWord ++ tailWord_4431416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4431435 : List Nat := [1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 7]
def baseStart_4431435 : Nat := 118140960795 + 4431435 * 2 ^ 59
def prefixEnd_4431435 : Nat := 4983230072969 + 3 ^ 40 * 4431435 * 2
def baseEnd_4431435 : Nat := 2275456144156974723882707

theorem tailTrace_4431435 : CollatzResearch.WordTrace tailWord_4431435 prefixEnd_4431435 2275456144156974723882707 := by
  unfold tailWord_4431435
  simp only [CollatzResearch.WordTrace]
  refine ⟨161627712700675298688887759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107751808467116865792591839 161627712700675298688887759)
  ·
    refine ⟨242441569051012948033331639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161627712700675298688887759 242441569051012948033331639)
    ·
      refine ⟨363662353576519422049997459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242441569051012948033331639 363662353576519422049997459)
      ·
        refine ⟨545493530364779133074996189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 363662353576519422049997459 545493530364779133074996189)
        ·
          refine ⟨204560073886792174903123571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 545493530364779133074996189 204560073886792174903123571)
          ·
            refine ⟨306840110830188262354685357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204560073886792174903123571 306840110830188262354685357)
            ·
              refine ⟨115065041561320598383007009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 306840110830188262354685357 115065041561320598383007009)
              ·
                refine ⟨86298781170990448787255257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115065041561320598383007009 86298781170990448787255257)
                ·
                  refine ⟨64724085878242836590441443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86298781170990448787255257 64724085878242836590441443)
                  ·
                    refine ⟨97086128817364254885662165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 64724085878242836590441443 97086128817364254885662165)
                    ·
                      refine ⟨2275456144156974723882707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 97086128817364254885662165 2275456144156974723882707)
                      ·
                        rfl

theorem cell23_4431435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 7].length) (baseStart_4431435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4431435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4431435 prefixEnd_4431435 := by exact prefixLift 4431435
  have htrace : WordTrace (prefixWord ++ tailWord_4431435) baseStart_4431435 baseEnd_4431435 := by
    simpa [prefixWord, tailWord_4431435, baseEnd_4431435] using wordTrace_append hprefix tailTrace_4431435
  have hstable : (prefixWord ++ tailWord_4431435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4431435).length < 2 ^ (prefixWord ++ tailWord_4431435).sum := by decide
  have hdescent : baseEnd_4431435 < baseStart_4431435 := by decide
  rcases family_descends (prefixWord ++ tailWord_4431435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4431459 : List Nat := [1, 1, 1, 5, 1, 3, 3, 2, 1, 5]
def baseStart_4431459 : Nat := 118140960795 + 4431459 * 2 ^ 59
def prefixEnd_4431459 : Nat := 4983230072969 + 3 ^ 40 * 4431459 * 2
def baseEnd_4431459 : Nat := 758489489230894209994199

theorem tailTrace_4431459 : CollatzResearch.WordTrace tailWord_4431459 prefixEnd_4431459 758489489230894209994199 := by
  unfold tailWord_4431459
  simp only [CollatzResearch.WordTrace]
  refine ⟨161628588052588350787761431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107752392035058900525174287 161628588052588350787761431)
  ·
    refine ⟨242442882078882526181642147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161628588052588350787761431 242442882078882526181642147)
    ·
      refine ⟨363664323118323789272463221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242442882078882526181642147 363664323118323789272463221)
      ·
        refine ⟨34093530292342855244293427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 363664323118323789272463221 34093530292342855244293427)
        ·
          refine ⟨51140295438514282866440141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34093530292342855244293427 51140295438514282866440141)
          ·
            refine ⟨19177610789442856074915053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51140295438514282866440141 19177610789442856074915053)
            ·
              refine ⟨7191604046041071028093145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19177610789442856074915053 7191604046041071028093145)
              ·
                refine ⟨5393703034530803271069859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7191604046041071028093145 5393703034530803271069859)
                ·
                  refine ⟨8090554551796204906604789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5393703034530803271069859 8090554551796204906604789)
                  ·
                    refine ⟨758489489230894209994199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8090554551796204906604789 758489489230894209994199)
                    ·
                      rfl

theorem cell23_4431459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 2, 1, 5].length) (baseStart_4431459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4431459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4431459 prefixEnd_4431459 := by exact prefixLift 4431459
  have htrace : WordTrace (prefixWord ++ tailWord_4431459) baseStart_4431459 baseEnd_4431459 := by
    simpa [prefixWord, tailWord_4431459, baseEnd_4431459] using wordTrace_append hprefix tailTrace_4431459
  have hstable : (prefixWord ++ tailWord_4431459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4431459).length < 2 ^ (prefixWord ++ tailWord_4431459).sum := by decide
  have hdescent : baseEnd_4431459 < baseStart_4431459 := by decide
  rcases family_descends (prefixWord ++ tailWord_4431459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4431466 : List Nat := [3, 1, 3, 2, 1, 2, 1, 3, 2, 3, 2]
def baseStart_4431466 : Nat := 118140960795 + 4431466 * 2 ^ 59
def prefixEnd_4431466 : Nat := 4983230072969 + 3 ^ 40 * 4431466 * 2
def baseEnd_4431466 : Nat := 2275472062057264102595065

theorem tailTrace_4431466 : CollatzResearch.WordTrace tailWord_4431466 prefixEnd_4431466 2275472062057264102595065 := by
  unfold tailWord_4431466
  simp only [CollatzResearch.WordTrace]
  refine ⟨40407210840890747745816563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107752562242375327322177501 40407210840890747745816563)
  ·
    refine ⟨60610816261336121618724845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40407210840890747745816563 60610816261336121618724845)
    ·
      refine ⟨22729056098001045607021817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60610816261336121618724845 22729056098001045607021817)
      ·
        refine ⟨17046792073500784205266363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22729056098001045607021817 17046792073500784205266363)
        ·
          refine ⟨25570188110251176307899545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17046792073500784205266363 25570188110251176307899545)
          ·
            refine ⟨19177641082688382230924659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25570188110251176307899545 19177641082688382230924659)
            ·
              refine ⟨28766461624032573346386989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19177641082688382230924659 28766461624032573346386989)
              ·
                refine ⟨10787423109012215004895121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28766461624032573346386989 10787423109012215004895121)
                ·
                  refine ⟨8090567331759161253671341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10787423109012215004895121 8090567331759161253671341)
                  ·
                    refine ⟨3033962749409685470126753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8090567331759161253671341 3033962749409685470126753)
                    ·
                      refine ⟨2275472062057264102595065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3033962749409685470126753 2275472062057264102595065)
                      ·
                        rfl

theorem cell23_4431466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_4431466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4431466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4431466 prefixEnd_4431466 := by exact prefixLift 4431466
  have htrace : WordTrace (prefixWord ++ tailWord_4431466) baseStart_4431466 baseEnd_4431466 := by
    simpa [prefixWord, tailWord_4431466, baseEnd_4431466] using wordTrace_append hprefix tailTrace_4431466
  have hstable : (prefixWord ++ tailWord_4431466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4431466).length < 2 ^ (prefixWord ++ tailWord_4431466).sum := by decide
  have hdescent : baseEnd_4431466 < baseStart_4431466 := by decide
  rcases family_descends (prefixWord ++ tailWord_4431466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4431472 : List Nat := [2, 1, 1, 1, 6, 1, 1, 1, 3, 6]
def baseStart_4431472 : Nat := 118140960795 + 4431472 * 2 ^ 59
def prefixEnd_4431472 : Nat := 4983230072969 + 3 ^ 40 * 4431472 * 2
def baseEnd_4431472 : Nat := 758491714313730359706679

theorem tailTrace_4431472 : CollatzResearch.WordTrace tailWord_4431472 prefixEnd_4431472 758491714313730359706679 := by
  unfold tailWord_4431472
  simp only [CollatzResearch.WordTrace]
  refine ⟨80814531100770627003992335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107752708134360836005323113 80814531100770627003992335)
  ·
    refine ⟨121221796651155940505988503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80814531100770627003992335 121221796651155940505988503)
    ·
      refine ⟨181832694976733910758982755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121221796651155940505988503 181832694976733910758982755)
      ·
        refine ⟨272749042465100866138474133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181832694976733910758982755 272749042465100866138474133)
        ·
          refine ⟨12785111365551603100240975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 272749042465100866138474133 12785111365551603100240975)
          ·
            refine ⟨19177667048327404650361463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12785111365551603100240975 19177667048327404650361463)
            ·
              refine ⟨28766500572491106975542195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19177667048327404650361463 28766500572491106975542195)
              ·
                refine ⟨43149750858736660463313293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28766500572491106975542195 43149750858736660463313293)
                ·
                  refine ⟨16181156572026247673742485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43149750858736660463313293 16181156572026247673742485)
                  ·
                    refine ⟨758491714313730359706679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16181156572026247673742485 758491714313730359706679)
                    ·
                      rfl

theorem cell23_4431472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 3, 6].length) (baseStart_4431472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4431472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4431472 prefixEnd_4431472 := by exact prefixLift 4431472
  have htrace : WordTrace (prefixWord ++ tailWord_4431472) baseStart_4431472 baseEnd_4431472 := by
    simpa [prefixWord, tailWord_4431472, baseEnd_4431472] using wordTrace_append hprefix tailTrace_4431472
  have hstable : (prefixWord ++ tailWord_4431472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4431472).length < 2 ^ (prefixWord ++ tailWord_4431472).sum := by decide
  have hdescent : baseEnd_4431472 < baseStart_4431472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4431472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4431482 : List Nat := [3, 1, 1, 1, 1, 1, 1, 7, 1, 1, 5]
def baseStart_4431482 : Nat := 118140960795 + 4431482 * 2 ^ 59
def prefixEnd_4431482 : Nat := 4983230072969 + 3 ^ 40 * 4431482 * 2
def baseEnd_4431482 : Nat := 2275480277747736039994991

theorem tailTrace_4431482 : CollatzResearch.WordTrace tailWord_4431482 prefixEnd_4431482 2275480277747736039994991 := by
  unfold tailWord_4431482
  simp only [CollatzResearch.WordTrace]
  refine ⟨40407356732876256428962175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107752951287670017143899133 40407356732876256428962175)
  ·
    refine ⟨60611035099314384643443263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40407356732876256428962175 60611035099314384643443263)
    ·
      refine ⟨90916552648971576965164895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60611035099314384643443263 90916552648971576965164895)
      ·
        refine ⟨136374828973457365447747343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90916552648971576965164895 136374828973457365447747343)
        ·
          refine ⟨204562243460186048171621015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136374828973457365447747343 204562243460186048171621015)
          ·
            refine ⟨306843365190279072257431523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204562243460186048171621015 306843365190279072257431523)
            ·
              refine ⟨460265047785418608386147285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 306843365190279072257431523 460265047785418608386147285)
              ·
                refine ⟨10787462057470748634050327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 460265047785418608386147285 10787462057470748634050327)
                ·
                  refine ⟨16181193086206122951075491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10787462057470748634050327 16181193086206122951075491)
                  ·
                    refine ⟨24271789629309184426613237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16181193086206122951075491 24271789629309184426613237)
                    ·
                      refine ⟨2275480277747736039994991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24271789629309184426613237 2275480277747736039994991)
                      ·
                        rfl

theorem cell23_4431482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7, 1, 1, 5].length) (baseStart_4431482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4431482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4431482 prefixEnd_4431482 := by exact prefixLift 4431482
  have htrace : WordTrace (prefixWord ++ tailWord_4431482) baseStart_4431482 baseEnd_4431482 := by
    simpa [prefixWord, tailWord_4431482, baseEnd_4431482] using wordTrace_append hprefix tailTrace_4431482
  have hstable : (prefixWord ++ tailWord_4431482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4431482).length < 2 ^ (prefixWord ++ tailWord_4431482).sum := by decide
  have hdescent : baseEnd_4431482 < baseStart_4431482 := by decide
  rcases family_descends (prefixWord ++ tailWord_4431482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4431506 : List Nat := [3, 2, 3, 1, 3, 1, 2, 1, 1, 6]
def baseStart_4431506 : Nat := 118140960795 + 4431506 * 2 ^ 59
def prefixEnd_4431506 : Nat := 4983230072969 + 3 ^ 40 * 4431506 * 2
def baseEnd_4431506 : Nat := 758497533761147982031627

theorem tailTrace_4431506 : CollatzResearch.WordTrace tailWord_4431506 prefixEnd_4431506 758497533761147982031627 := by
  unfold tailWord_4431506
  simp only [CollatzResearch.WordTrace]
  refine ⟨40407575570854519453680593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107753534855612051876481581 40407575570854519453680593)
  ·
    refine ⟨30305681678140889590260445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40407575570854519453680593 30305681678140889590260445)
    ·
      refine ⟨11364630629302833596347667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30305681678140889590260445 11364630629302833596347667)
      ·
        refine ⟨17046945943954250394521501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11364630629302833596347667 17046945943954250394521501)
        ·
          refine ⟨6392604728982843897945563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17046945943954250394521501 6392604728982843897945563)
          ·
            refine ⟨9588907093474265846918345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6392604728982843897945563 9588907093474265846918345)
            ·
              refine ⟨7191680320105699385188759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9588907093474265846918345 7191680320105699385188759)
              ·
                refine ⟨10787520480158549077783139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7191680320105699385188759 10787520480158549077783139)
                ·
                  refine ⟨16181280720237823616674709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10787520480158549077783139 16181280720237823616674709)
                  ·
                    refine ⟨758497533761147982031627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16181280720237823616674709 758497533761147982031627)
                    ·
                      rfl

theorem cell23_4431506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_4431506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4431506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4431506 prefixEnd_4431506 := by exact prefixLift 4431506
  have htrace : WordTrace (prefixWord ++ tailWord_4431506) baseStart_4431506 baseEnd_4431506 := by
    simpa [prefixWord, tailWord_4431506, baseEnd_4431506] using wordTrace_append hprefix tailTrace_4431506
  have hstable : (prefixWord ++ tailWord_4431506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4431506).length < 2 ^ (prefixWord ++ tailWord_4431506).sum := by decide
  have hdescent : baseEnd_4431506 < baseStart_4431506 := by decide
  rcases family_descends (prefixWord ++ tailWord_4431506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4431546 : List Nat := [3, 1, 1, 1, 2, 5, 1, 1, 4, 1, 3]
def baseStart_4431546 : Nat := 118140960795 + 4431546 * 2 ^ 59
def prefixEnd_4431546 : Nat := 4983230072969 + 3 ^ 40 * 4431546 * 2
def baseEnd_4431546 : Nat := 2275513140509623789594697

theorem tailTrace_4431546 : CollatzResearch.WordTrace tailWord_4431546 prefixEnd_4431546 2275513140509623789594697 := by
  unfold tailWord_4431546
  simp only [CollatzResearch.WordTrace]
  refine ⟨40407940300818291161544623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107754507468848776430785661 40407940300818291161544623)
  ·
    refine ⟨60611910451227436742316935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40407940300818291161544623 60611910451227436742316935)
    ·
      refine ⟨90917865676841155113475403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60611910451227436742316935 90917865676841155113475403)
      ·
        refine ⟨136376798515261732670213105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90917865676841155113475403 136376798515261732670213105)
        ·
          refine ⟨102282598886446299502659829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136376798515261732670213105 102282598886446299502659829)
          ·
            refine ⟨9588993645604340578374359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 102282598886446299502659829 9588993645604340578374359)
            ·
              refine ⟨14383490468406510867561539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9588993645604340578374359 14383490468406510867561539)
              ·
                refine ⟨21575235702609766301342309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14383490468406510867561539 21575235702609766301342309)
                ·
                  refine ⟨4045356694239331181501683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21575235702609766301342309 4045356694239331181501683)
                  ·
                    refine ⟨6068035041358996772252525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4045356694239331181501683 6068035041358996772252525)
                    ·
                      refine ⟨2275513140509623789594697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6068035041358996772252525 2275513140509623789594697)
                      ·
                        rfl

theorem cell23_4431546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 4, 1, 3].length) (baseStart_4431546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4431546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4431546 prefixEnd_4431546 := by exact prefixLift 4431546
  have htrace : WordTrace (prefixWord ++ tailWord_4431546) baseStart_4431546 baseEnd_4431546 := by
    simpa [prefixWord, tailWord_4431546, baseEnd_4431546] using wordTrace_append hprefix tailTrace_4431546
  have hstable : (prefixWord ++ tailWord_4431546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4431546).length < 2 ^ (prefixWord ++ tailWord_4431546).sum := by decide
  have hdescent : baseEnd_4431546 < baseStart_4431546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4431546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4431581 : List Nat := [1, 4, 3, 3, 2, 1, 1, 3, 1, 2, 2]
def baseStart_4431581 : Nat := 118140960795 + 4431581 * 2 ^ 59
def prefixEnd_4431581 : Nat := 4983230072969 + 3 ^ 40 * 4431581 * 2
def baseEnd_4431581 : Nat := 2275531112332531152657037

theorem tailTrace_4431581 : CollatzResearch.WordTrace tailWord_4431581 prefixEnd_4431581 2275531112332531152657037 := by
  unfold tailWord_4431581
  simp only [CollatzResearch.WordTrace]
  refine ⟨161633037758146365623702597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107755358505430910415801731 161633037758146365623702597)
  ·
    refine ⟨30306194579652443554444237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 161633037758146365623702597 30306194579652443554444237)
    ·
      refine ⟨11364822967369666332916589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30306194579652443554444237 11364822967369666332916589)
      ·
        refine ⟨4261808612763624874843721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11364822967369666332916589 4261808612763624874843721)
        ·
          refine ⟨3196356459572718656132791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4261808612763624874843721 3196356459572718656132791)
          ·
            refine ⟨4794534689359077984199187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3196356459572718656132791 4794534689359077984199187)
            ·
              refine ⟨7191802034038616976298781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4794534689359077984199187 7191802034038616976298781)
              ·
                refine ⟨2696925762764481366112043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7191802034038616976298781 2696925762764481366112043)
                ·
                  refine ⟨4045388644146722049168065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2696925762764481366112043 4045388644146722049168065)
                  ·
                    refine ⟨3034041483110041536876049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4045388644146722049168065 3034041483110041536876049)
                    ·
                      refine ⟨2275531112332531152657037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3034041483110041536876049 2275531112332531152657037)
                      ·
                        rfl

theorem cell23_4431581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_4431581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4431581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4431581 prefixEnd_4431581 := by exact prefixLift 4431581
  have htrace : WordTrace (prefixWord ++ tailWord_4431581) baseStart_4431581 baseEnd_4431581 := by
    simpa [prefixWord, tailWord_4431581, baseEnd_4431581] using wordTrace_append hprefix tailTrace_4431581
  have hstable : (prefixWord ++ tailWord_4431581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4431581).length < 2 ^ (prefixWord ++ tailWord_4431581).sum := by decide
  have hdescent : baseEnd_4431581 < baseStart_4431581 := by decide
  rcases family_descends (prefixWord ++ tailWord_4431581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4431589 : List Nat := [1, 3, 1, 4, 1, 1, 3, 1, 2, 1, 5]
def baseStart_4431589 : Nat := 118140960795 + 4431589 * 2 ^ 59
def prefixEnd_4431589 : Nat := 4983230072969 + 3 ^ 40 * 4431589 * 2
def baseEnd_4431589 : Nat := 2275535220177767121356999

theorem tailTrace_4431589 : CollatzResearch.WordTrace tailWord_4431589 prefixEnd_4431589 2275535220177767121356999 := by
  unfold tailWord_4431589
  simp only [CollatzResearch.WordTrace]
  refine ⟨161633329542117382989993821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107755553028078255326662547 161633329542117382989993821)
  ·
    refine ⟨60612498578294018621247683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161633329542117382989993821 60612498578294018621247683)
    ·
      refine ⟨90918747867441027931871525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60612498578294018621247683 90918747867441027931871525)
      ·
        refine ⟨17047265225145192737225911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90918747867441027931871525 17047265225145192737225911)
        ·
          refine ⟨25570897837717789105838867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17047265225145192737225911 25570897837717789105838867)
          ·
            refine ⟨38356346756576683658758301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25570897837717789105838867 38356346756576683658758301)
            ·
              refine ⟨14383630033716256372034363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38356346756576683658758301 14383630033716256372034363)
              ·
                refine ⟨21575445050574384558051545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14383630033716256372034363 21575445050574384558051545)
                ·
                  refine ⟨16181583787930788418538659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21575445050574384558051545 16181583787930788418538659)
                  ·
                    refine ⟨24272375681896182627807989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16181583787930788418538659 24272375681896182627807989)
                    ·
                      refine ⟨2275535220177767121356999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24272375681896182627807989 2275535220177767121356999)
                      ·
                        rfl

theorem cell23_4431589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_4431589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4431589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4431589 prefixEnd_4431589 := by exact prefixLift 4431589
  have htrace : WordTrace (prefixWord ++ tailWord_4431589) baseStart_4431589 baseEnd_4431589 := by
    simpa [prefixWord, tailWord_4431589, baseEnd_4431589] using wordTrace_append hprefix tailTrace_4431589
  have hstable : (prefixWord ++ tailWord_4431589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4431589).length < 2 ^ (prefixWord ++ tailWord_4431589).sum := by decide
  have hdescent : baseEnd_4431589 < baseStart_4431589 := by decide
  rcases family_descends (prefixWord ++ tailWord_4431589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4431614 : List Nat := [4, 2, 2, 1, 4, 1, 2, 1, 2, 1, 3]
def baseStart_4431614 : Nat := 118140960795 + 4431614 * 2 ^ 59
def prefixEnd_4431614 : Nat := 4983230072969 + 3 ^ 40 * 4431614 * 2
def baseEnd_4431614 : Nat := 2275548057194129523544385

theorem tailTrace_4431614 : CollatzResearch.WordTrace tailWord_4431614 prefixEnd_4431614 2275548057194129523544385 := by
  unfold tailWord_4431614
  simp only [CollatzResearch.WordTrace]
  refine ⟨20204280170878351532456737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107756160911351208173102597 20204280170878351532456737)
  ·
    refine ⟨15153210128158763649342553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20204280170878351532456737 15153210128158763649342553)
    ·
      refine ⟨11364907596119072737006915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15153210128158763649342553 11364907596119072737006915)
      ·
        refine ⟨17047361394178609105510373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11364907596119072737006915 17047361394178609105510373)
        ·
          refine ⟨3196380261408489207283195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17047361394178609105510373 3196380261408489207283195)
          ·
            refine ⟨4794570392112733810924793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3196380261408489207283195 4794570392112733810924793)
            ·
              refine ⟨3595927794084550358193595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4794570392112733810924793 3595927794084550358193595)
              ·
                refine ⟨5393891691126825537290393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3595927794084550358193595 5393891691126825537290393)
                ·
                  refine ⟨4045418768345119152967795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5393891691126825537290393 4045418768345119152967795)
                  ·
                    refine ⟨6068128152517678729451693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4045418768345119152967795 6068128152517678729451693)
                    ·
                      refine ⟨2275548057194129523544385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6068128152517678729451693 2275548057194129523544385)
                      ·
                        rfl

theorem cell23_4431614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_4431614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4431614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4431614 prefixEnd_4431614 := by exact prefixLift 4431614
  have htrace : WordTrace (prefixWord ++ tailWord_4431614) baseStart_4431614 baseEnd_4431614 := by
    simpa [prefixWord, tailWord_4431614, baseEnd_4431614] using wordTrace_append hprefix tailTrace_4431614
  have hstable : (prefixWord ++ tailWord_4431614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4431614).length < 2 ^ (prefixWord ++ tailWord_4431614).sum := by decide
  have hdescent : baseEnd_4431614 < baseStart_4431614 := by decide
  rcases family_descends (prefixWord ++ tailWord_4431614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4431619 : List Nat := [1, 1, 1, 3, 2, 2, 2, 3, 2, 3, 3]
def baseStart_4431619 : Nat := 118140960795 + 4431619 * 2 ^ 59
def prefixEnd_4431619 : Nat := 4983230072969 + 3 ^ 40 * 4431619 * 2
def baseEnd_4431619 : Nat := 2275550624597402003981861

theorem tailTrace_4431619 : CollatzResearch.WordTrace tailWord_4431619 prefixEnd_4431619 2275550624597402003981861 := by
  unfold tailWord_4431619
  simp only [CollatzResearch.WordTrace]
  refine ⟨161634423732008698113585911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107756282488005798742390607 161634423732008698113585911)
  ·
    refine ⟨242451635598013047170378867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161634423732008698113585911 242451635598013047170378867)
    ·
      refine ⟨363677453397019570755568301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242451635598013047170378867 363677453397019570755568301)
      ·
        refine ⟨136379045023882339033338113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 363677453397019570755568301 136379045023882339033338113)
        ·
          refine ⟨102284283767911754275003585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136379045023882339033338113 102284283767911754275003585)
          ·
            refine ⟨76713212825933815706252689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102284283767911754275003585 76713212825933815706252689)
            ·
              refine ⟨57534909619450361779689517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76713212825933815706252689 57534909619450361779689517)
              ·
                refine ⟨21575591107293885667383569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57534909619450361779689517 21575591107293885667383569)
                ·
                  refine ⟨16181693330470414250537677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21575591107293885667383569 16181693330470414250537677)
                  ·
                    refine ⟨6068134998926405343951629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16181693330470414250537677 6068134998926405343951629)
                    ·
                      refine ⟨2275550624597402003981861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6068134998926405343951629 2275550624597402003981861)
                      ·
                        rfl

theorem cell23_4431619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 2, 3, 3].length) (baseStart_4431619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4431619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4431619 prefixEnd_4431619 := by exact prefixLift 4431619
  have htrace : WordTrace (prefixWord ++ tailWord_4431619) baseStart_4431619 baseEnd_4431619 := by
    simpa [prefixWord, tailWord_4431619, baseEnd_4431619] using wordTrace_append hprefix tailTrace_4431619
  have hstable : (prefixWord ++ tailWord_4431619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4431619).length < 2 ^ (prefixWord ++ tailWord_4431619).sum := by decide
  have hdescent : baseEnd_4431619 < baseStart_4431619 := by decide
  rcases family_descends (prefixWord ++ tailWord_4431619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4431620 : List Nat := [2, 3, 2, 2, 1, 3, 1, 3, 2, 2, 2]
def baseStart_4431620 : Nat := 118140960795 + 4431620 * 2 ^ 59
def prefixEnd_4431620 : Nat := 4983230072969 + 3 ^ 40 * 4431620 * 2
def baseEnd_4431620 : Nat := 2275551138078056500069357

theorem tailTrace_4431620 : CollatzResearch.WordTrace tailWord_4431620 prefixEnd_4431620 2275551138078056500069357 := by
  unfold tailWord_4431620
  simp only [CollatzResearch.WordTrace]
  refine ⟨80817230102502537642186157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107756306803336716856248209 80817230102502537642186157)
  ·
    refine ⟨30306461288438451615819809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80817230102502537642186157 30306461288438451615819809)
    ·
      refine ⟨22729845966328838711864857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30306461288438451615819809 22729845966328838711864857)
      ·
        refine ⟨17047384474746629033898643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22729845966328838711864857 17047384474746629033898643)
        ·
          refine ⟨25571076712119943550847965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17047384474746629033898643 25571076712119943550847965)
          ·
            refine ⟨9589153767044978831567987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25571076712119943550847965 9589153767044978831567987)
            ·
              refine ⟨14383730650567468247351981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9589153767044978831567987 14383730650567468247351981)
              ·
                refine ⟨5393898993962800592756993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14383730650567468247351981 5393898993962800592756993)
                ·
                  refine ⟨4045424245472100444567745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5393898993962800592756993 4045424245472100444567745)
                  ·
                    refine ⟨3034068184104075333425809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4045424245472100444567745 3034068184104075333425809)
                    ·
                      refine ⟨2275551138078056500069357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3034068184104075333425809 2275551138078056500069357)
                      ·
                        rfl

theorem cell23_4431620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_4431620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4431620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4431620 prefixEnd_4431620 := by exact prefixLift 4431620
  have htrace : WordTrace (prefixWord ++ tailWord_4431620) baseStart_4431620 baseEnd_4431620 := by
    simpa [prefixWord, tailWord_4431620, baseEnd_4431620] using wordTrace_append hprefix tailTrace_4431620
  have hstable : (prefixWord ++ tailWord_4431620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4431620).length < 2 ^ (prefixWord ++ tailWord_4431620).sum := by decide
  have hdescent : baseEnd_4431620 < baseStart_4431620 := by decide
  rcases family_descends (prefixWord ++ tailWord_4431620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4431649 : List Nat := [1, 2, 3, 2, 1, 3, 1, 2, 1, 2, 5]
def baseStart_4431649 : Nat := 118140960795 + 4431649 * 2 ^ 59
def prefixEnd_4431649 : Nat := 4983230072969 + 3 ^ 40 * 4431649 * 2
def baseEnd_4431649 : Nat := 2275566029017036886606723

theorem tailTrace_4431649 : CollatzResearch.WordTrace tailWord_4431649 prefixEnd_4431649 2275566029017036886606723 := by
  unfold tailWord_4431649
  simp only [CollatzResearch.WordTrace]
  refine ⟨161635517921900013237178001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107757011947933342158118667 161635517921900013237178001)
  ·
    refine ⟨121226638441425009927883501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161635517921900013237178001 121226638441425009927883501)
    ·
      refine ⟨45459989415534378722956313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121226638441425009927883501 45459989415534378722956313)
      ·
        refine ⟨34094992061650784042217235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45459989415534378722956313 34094992061650784042217235)
        ·
          refine ⟨51142488092476176063325853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34094992061650784042217235 51142488092476176063325853)
          ·
            refine ⟨19178433034678566023747195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51142488092476176063325853 19178433034678566023747195)
            ·
              refine ⟨28767649552017849035620793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19178433034678566023747195 28767649552017849035620793)
              ·
                refine ⟨21575737164013386776715595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28767649552017849035620793 21575737164013386776715595)
                ·
                  refine ⟨32363605746020080165073393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21575737164013386776715595 32363605746020080165073393)
                  ·
                    refine ⟨24272704309515060123805045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32363605746020080165073393 24272704309515060123805045)
                    ·
                      refine ⟨2275566029017036886606723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24272704309515060123805045 2275566029017036886606723)
                      ·
                        rfl

theorem cell23_4431649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_4431649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4431649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4431649 prefixEnd_4431649 := by exact prefixLift 4431649
  have htrace : WordTrace (prefixWord ++ tailWord_4431649) baseStart_4431649 baseEnd_4431649 := by
    simpa [prefixWord, tailWord_4431649, baseEnd_4431649] using wordTrace_append hprefix tailTrace_4431649
  have hstable : (prefixWord ++ tailWord_4431649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4431649).length < 2 ^ (prefixWord ++ tailWord_4431649).sum := by decide
  have hdescent : baseEnd_4431649 < baseStart_4431649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4431649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4431656 : List Nat := [2, 1, 5, 1, 1, 2, 2, 2, 2, 5]
def baseStart_4431656 : Nat := 118140960795 + 4431656 * 2 ^ 59
def prefixEnd_4431656 : Nat := 4983230072969 + 3 ^ 40 * 4431656 * 2
def baseEnd_4431656 : Nat := 758523207793872786406397

theorem tailTrace_4431656 : CollatzResearch.WordTrace tailWord_4431656 prefixEnd_4431656 758523207793872786406397 := by
  unfold tailWord_4431656
  simp only [CollatzResearch.WordTrace]
  refine ⟨80817886616437326716341411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107757182155249768955121881 80817886616437326716341411)
  ·
    refine ⟨121226829924655990074512117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80817886616437326716341411 121226829924655990074512117)
    ·
      refine ⟨11365015305436499069485511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 121226829924655990074512117 11365015305436499069485511)
      ·
        refine ⟨17047522958154748604228267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11365015305436499069485511 17047522958154748604228267)
        ·
          refine ⟨25571284437232122906342401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17047522958154748604228267 25571284437232122906342401)
          ·
            refine ⟨19178463327924092179756801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25571284437232122906342401 19178463327924092179756801)
            ·
              refine ⟨14383847495943069134817601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19178463327924092179756801 14383847495943069134817601)
              ·
                refine ⟨10787885621957301851113201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14383847495943069134817601 10787885621957301851113201)
                ·
                  refine ⟨8090914216467976388334901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10787885621957301851113201 8090914216467976388334901)
                  ·
                    refine ⟨758523207793872786406397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8090914216467976388334901 758523207793872786406397)
                    ·
                      rfl

theorem cell23_4431656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_4431656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4431656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4431656 prefixEnd_4431656 := by exact prefixLift 4431656
  have htrace : WordTrace (prefixWord ++ tailWord_4431656) baseStart_4431656 baseEnd_4431656 := by
    simpa [prefixWord, tailWord_4431656, baseEnd_4431656] using wordTrace_append hprefix tailTrace_4431656
  have hstable : (prefixWord ++ tailWord_4431656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4431656).length < 2 ^ (prefixWord ++ tailWord_4431656).sum := by decide
  have hdescent : baseEnd_4431656 < baseStart_4431656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4431656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4431676 : List Nat := [2, 2, 2, 2, 1, 1, 3, 1, 1, 6, 2]
def baseStart_4431676 : Nat := 118140960795 + 4431676 * 2 ^ 59
def prefixEnd_4431676 : Nat := 4983230072969 + 3 ^ 40 * 4431676 * 2
def baseEnd_4431676 : Nat := 2275579892994708280969099

theorem tailTrace_4431676 : CollatzResearch.WordTrace tailWord_4431676 prefixEnd_4431676 2275579892994708280969099 := by
  unfold tailWord_4431676
  simp only [CollatzResearch.WordTrace]
  refine ⟨80818251346401098424205441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107757668461868131232273921 80818251346401098424205441)
  ·
    refine ⟨60613688509800823818154081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80818251346401098424205441 60613688509800823818154081)
    ·
      refine ⟨45460266382350617863615561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60613688509800823818154081 45460266382350617863615561)
      ·
        refine ⟨34095199786762963397711671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45460266382350617863615561 34095199786762963397711671)
        ·
          refine ⟨51142799680144445096567507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34095199786762963397711671 51142799680144445096567507)
          ·
            refine ⟨76714199520216667644851261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51142799680144445096567507 76714199520216667644851261)
            ·
              refine ⟨28767824820081250366819223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76714199520216667644851261 28767824820081250366819223)
              ·
                refine ⟨43151737230121875550228835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28767824820081250366819223 43151737230121875550228835)
                ·
                  refine ⟨64727605845182813325343253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43151737230121875550228835 64727605845182813325343253)
                  ·
                    refine ⟨3034106523992944374625465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 64727605845182813325343253 3034106523992944374625465)
                    ·
                      refine ⟨2275579892994708280969099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3034106523992944374625465 2275579892994708280969099)
                      ·
                        rfl

theorem cell23_4431676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 1, 6, 2].length) (baseStart_4431676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4431676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4431676 prefixEnd_4431676 := by exact prefixLift 4431676
  have htrace : WordTrace (prefixWord ++ tailWord_4431676) baseStart_4431676 baseEnd_4431676 := by
    simpa [prefixWord, tailWord_4431676, baseEnd_4431676] using wordTrace_append hprefix tailTrace_4431676
  have hstable : (prefixWord ++ tailWord_4431676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4431676).length < 2 ^ (prefixWord ++ tailWord_4431676).sum := by decide
  have hdescent : baseEnd_4431676 < baseStart_4431676 := by decide
  rcases family_descends (prefixWord ++ tailWord_4431676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4431693 : List Nat := [1, 6, 1, 2, 1, 2, 1, 1, 1, 3, 4]
def baseStart_4431693 : Nat := 118140960795 + 4431693 * 2 ^ 59
def prefixEnd_4431693 : Nat := 4983230072969 + 3 ^ 40 * 4431693 * 2
def baseEnd_4431693 : Nat := 2275588622165834714456521

theorem tailTrace_4431693 : CollatzResearch.WordTrace tailWord_4431693 prefixEnd_4431693 2275588622165834714456521 := by
  unfold tailWord_4431693
  simp only [CollatzResearch.WordTrace]
  refine ⟨161637122733740608751779733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107758081822493739167853155 161637122733740608751779733)
  ·
    refine ⟨7576740128144091035239675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 161637122733740608751779733 7576740128144091035239675)
    ·
      refine ⟨11365110192216136552859513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7576740128144091035239675 11365110192216136552859513)
      ·
        refine ⟨8523832644162102414644635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11365110192216136552859513 8523832644162102414644635)
        ·
          refine ⟨12785748966243153621966953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8523832644162102414644635 12785748966243153621966953)
          ·
            refine ⟨9589311724682365216475215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12785748966243153621966953 9589311724682365216475215)
            ·
              refine ⟨14383967587023547824712823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9589311724682365216475215 14383967587023547824712823)
              ·
                refine ⟨21575951380535321737069235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14383967587023547824712823 21575951380535321737069235)
                ·
                  refine ⟨32363927070802982605603853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21575951380535321737069235 32363927070802982605603853)
                  ·
                    refine ⟨12136472651551118477101445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32363927070802982605603853 12136472651551118477101445)
                    ·
                      refine ⟨2275588622165834714456521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12136472651551118477101445 2275588622165834714456521)
                      ·
                        rfl

theorem cell23_4431693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_4431693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4431693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4431693 prefixEnd_4431693 := by exact prefixLift 4431693
  have htrace : WordTrace (prefixWord ++ tailWord_4431693) baseStart_4431693 baseEnd_4431693 := by
    simpa [prefixWord, tailWord_4431693, baseEnd_4431693] using wordTrace_append hprefix tailTrace_4431693
  have hstable : (prefixWord ++ tailWord_4431693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4431693).length < 2 ^ (prefixWord ++ tailWord_4431693).sum := by decide
  have hdescent : baseEnd_4431693 < baseStart_4431693 := by decide
  rcases family_descends (prefixWord ++ tailWord_4431693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4431716 : List Nat := [2, 3, 1, 1, 5, 1, 1, 1, 8]
def baseStart_4431716 : Nat := 118140960795 + 4431716 * 2 ^ 59
def prefixEnd_4431716 : Nat := 4983230072969 + 3 ^ 40 * 4431716 * 2
def baseEnd_4431716 : Nat := 252844492468987569385435

theorem tailTrace_4431716 : CollatzResearch.WordTrace tailWord_4431716 prefixEnd_4431716 252844492468987569385435 := by
  unfold tailWord_4431716
  simp only [CollatzResearch.WordTrace]
  refine ⟨80818980806328641839933501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107758641075104855786578001 80818980806328641839933501)
  ·
    refine ⟨30307117802373240689975063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80818980806328641839933501 30307117802373240689975063)
    ·
      refine ⟨45460676703559861034962595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30307117802373240689975063 45460676703559861034962595)
      ·
        refine ⟨68191015055339791552443893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45460676703559861034962595 68191015055339791552443893)
        ·
          refine ⟨6392907661438105458041615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68191015055339791552443893 6392907661438105458041615)
          ·
            refine ⟨9589361492157158187062423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6392907661438105458041615 9589361492157158187062423)
            ·
              refine ⟨14384042238235737280593635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9589361492157158187062423 14384042238235737280593635)
              ·
                refine ⟨21576063357353605920890453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14384042238235737280593635 21576063357353605920890453)
                ·
                  refine ⟨252844492468987569385435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21576063357353605920890453 252844492468987569385435)
                  ·
                    rfl

theorem cell23_4431716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 8].length) (baseStart_4431716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4431716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4431716 prefixEnd_4431716 := by exact prefixLift 4431716
  have htrace : WordTrace (prefixWord ++ tailWord_4431716) baseStart_4431716 baseEnd_4431716 := by
    simpa [prefixWord, tailWord_4431716, baseEnd_4431716] using wordTrace_append hprefix tailTrace_4431716
  have hstable : (prefixWord ++ tailWord_4431716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4431716).length < 2 ^ (prefixWord ++ tailWord_4431716).sum := by decide
  have hdescent : baseEnd_4431716 < baseStart_4431716 := by decide
  rcases family_descends (prefixWord ++ tailWord_4431716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4431719 : List Nat := [1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 8]
def baseStart_4431719 : Nat := 118140960795 + 4431719 * 2 ^ 59
def prefixEnd_4431719 : Nat := 4983230072969 + 3 ^ 40 * 4431719 * 2
def baseEnd_4431719 : Nat := 2275601972662851612731401

theorem tailTrace_4431719 : CollatzResearch.WordTrace tailWord_4431719 prefixEnd_4431719 2275601972662851612731401 := by
  unfold tailWord_4431719
  simp only [CollatzResearch.WordTrace]
  refine ⟨161638071031646415192226211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107758714021097610128150807 161638071031646415192226211)
  ·
    refine ⟨242457106547469622788339317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161638071031646415192226211 242457106547469622788339317)
    ·
      refine ⟨22730353738825277136406811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 242457106547469622788339317 22730353738825277136406811)
      ·
        refine ⟨34095530608237915704610217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22730353738825277136406811 34095530608237915704610217)
        ·
          refine ⟨25571647956178436778457663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34095530608237915704610217 25571647956178436778457663)
          ·
            refine ⟨38357471934267655167686495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25571647956178436778457663 38357471934267655167686495)
            ·
              refine ⟨57536207901401482751529743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38357471934267655167686495 57536207901401482751529743)
              ·
                refine ⟨86304311852102224127294615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57536207901401482751529743 86304311852102224127294615)
                ·
                  refine ⟨129456467778153336190941923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86304311852102224127294615 129456467778153336190941923)
                  ·
                    refine ⟨194184701667230004286412885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 129456467778153336190941923 194184701667230004286412885)
                    ·
                      refine ⟨2275601972662851612731401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 194184701667230004286412885 2275601972662851612731401)
                      ·
                        rfl

theorem cell23_4431719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_4431719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4431719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4431719 prefixEnd_4431719 := by exact prefixLift 4431719
  have htrace : WordTrace (prefixWord ++ tailWord_4431719) baseStart_4431719 baseEnd_4431719 := by
    simpa [prefixWord, tailWord_4431719, baseEnd_4431719] using wordTrace_append hprefix tailTrace_4431719
  have hstable : (prefixWord ++ tailWord_4431719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4431719).length < 2 ^ (prefixWord ++ tailWord_4431719).sum := by decide
  have hdescent : baseEnd_4431719 < baseStart_4431719 := by decide
  rcases family_descends (prefixWord ++ tailWord_4431719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4431733 : List Nat := [1, 3, 4, 1, 1, 1, 5, 1, 6]
def baseStart_4431733 : Nat := 118140960795 + 4431733 * 2 ^ 59
def prefixEnd_4431733 : Nat := 4983230072969 + 3 ^ 40 * 4431733 * 2
def baseEnd_4431733 : Nat := 252845462376890506439593

theorem tailTrace_4431733 : CollatzResearch.WordTrace tailWord_4431733 prefixEnd_4431733 252845462376890506439593 := by
  unfold tailWord_4431733
  simp only [CollatzResearch.WordTrace]
  refine ⟨161638581653595695583235853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107759054435730463722157235 161638581653595695583235853)
  ·
    refine ⟨60614468120098385843713445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161638581653595695583235853 60614468120098385843713445)
    ·
      refine ⟨11365212772518447345696271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60614468120098385843713445 11365212772518447345696271)
      ·
        refine ⟨17047819158777671018544407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11365212772518447345696271 17047819158777671018544407)
        ·
          refine ⟨25571728738166506527816611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17047819158777671018544407 25571728738166506527816611)
          ·
            refine ⟨38357593107249759791724917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25571728738166506527816611 38357593107249759791724917)
            ·
              refine ⟨3596024353804664980474211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38357593107249759791724917 3596024353804664980474211)
              ·
                refine ⟨5394036530706997470711317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3596024353804664980474211 5394036530706997470711317)
                ·
                  refine ⟨252845462376890506439593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5394036530706997470711317 252845462376890506439593)
                  ·
                    rfl

theorem cell23_4431733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5, 1, 6].length) (baseStart_4431733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4431733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4431733 prefixEnd_4431733 := by exact prefixLift 4431733
  have htrace : WordTrace (prefixWord ++ tailWord_4431733) baseStart_4431733 baseEnd_4431733 := by
    simpa [prefixWord, tailWord_4431733, baseEnd_4431733] using wordTrace_append hprefix tailTrace_4431733
  have hstable : (prefixWord ++ tailWord_4431733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4431733).length < 2 ^ (prefixWord ++ tailWord_4431733).sum := by decide
  have hdescent : baseEnd_4431733 < baseStart_4431733 := by decide
  rcases family_descends (prefixWord ++ tailWord_4431733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4431753 : List Nat := [1, 2, 1, 1, 5, 1, 2, 3, 2, 3, 2]
def baseStart_4431753 : Nat := 118140960795 + 4431753 * 2 ^ 59
def prefixEnd_4431753 : Nat := 4983230072969 + 3 ^ 40 * 4431753 * 2
def baseEnd_4431753 : Nat := 2275619431005104479706245

theorem tailTrace_4431753 : CollatzResearch.WordTrace tailWord_4431753 prefixEnd_4431753 2275619431005104479706245 := by
  unfold tailWord_4431753
  simp only [CollatzResearch.WordTrace]
  refine ⟨161639311113523238998963913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107759540742348825999309275 161639311113523238998963913)
  ·
    refine ⟨121229483335142429249222935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161639311113523238998963913 121229483335142429249222935)
    ·
      refine ⟨181844225002713643873834403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121229483335142429249222935 181844225002713643873834403)
      ·
        refine ⟨272766337504070465810751605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181844225002713643873834403 272766337504070465810751605)
        ·
          refine ⟨25571844141006606169757963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 272766337504070465810751605 25571844141006606169757963)
          ·
            refine ⟨38357766211509909254636945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25571844141006606169757963 38357766211509909254636945)
            ·
              refine ⟨28768324658632431940977709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38357766211509909254636945 28768324658632431940977709)
              ·
                refine ⟨10788121746987161977866641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28768324658632431940977709 10788121746987161977866641)
                ·
                  refine ⟨8091091310240371483399981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10788121746987161977866641 8091091310240371483399981)
                  ·
                    refine ⟨3034159241340139306274993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8091091310240371483399981 3034159241340139306274993)
                    ·
                      refine ⟨2275619431005104479706245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3034159241340139306274993 2275619431005104479706245)
                      ·
                        rfl

theorem cell23_4431753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 3, 2, 3, 2].length) (baseStart_4431753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4431753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4431753 prefixEnd_4431753 := by exact prefixLift 4431753
  have htrace : WordTrace (prefixWord ++ tailWord_4431753) baseStart_4431753 baseEnd_4431753 := by
    simpa [prefixWord, tailWord_4431753, baseEnd_4431753] using wordTrace_append hprefix tailTrace_4431753
  have hstable : (prefixWord ++ tailWord_4431753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4431753).length < 2 ^ (prefixWord ++ tailWord_4431753).sum := by decide
  have hdescent : baseEnd_4431753 < baseStart_4431753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4431753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4431754 : List Nat := [3, 1, 2, 4, 3, 1, 1, 3, 1, 4]
def baseStart_4431754 : Nat := 118140960795 + 4431754 * 2 ^ 59
def prefixEnd_4431754 : Nat := 4983230072969 + 3 ^ 40 * 4431754 * 2
def baseEnd_4431754 : Nat := 758539981495252991931247

theorem tailTrace_4431754 : CollatzResearch.WordTrace tailWord_4431754 prefixEnd_4431754 758539981495252991931247 := by
  unfold tailWord_4431754
  simp only [CollatzResearch.WordTrace]
  refine ⟨40409836896629904042437579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107759565057679744113166877 40409836896629904042437579)
  ·
    refine ⟨60614755344944856063656369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40409836896629904042437579 60614755344944856063656369)
    ·
      refine ⟨45461066508708642047742277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60614755344944856063656369 45461066508708642047742277)
      ·
        refine ⟨8523949970382870383951677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45461066508708642047742277 8523949970382870383951677)
        ·
          refine ⟨3196481238893576393981879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8523949970382870383951677 3196481238893576393981879)
          ·
            refine ⟨4794721858340364590972819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3196481238893576393981879 4794721858340364590972819)
            ·
              refine ⟨7192082787510546886459229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4794721858340364590972819 7192082787510546886459229)
              ·
                refine ⟨2697031045316455082422211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7192082787510546886459229 2697031045316455082422211)
                ·
                  refine ⟨4045546567974682623633317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2697031045316455082422211 4045546567974682623633317)
                  ·
                    refine ⟨758539981495252991931247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4045546567974682623633317 758539981495252991931247)
                    ·
                      rfl

theorem cell23_4431754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 3, 1, 4].length) (baseStart_4431754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4431754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4431754 prefixEnd_4431754 := by exact prefixLift 4431754
  have htrace : WordTrace (prefixWord ++ tailWord_4431754) baseStart_4431754 baseEnd_4431754 := by
    simpa [prefixWord, tailWord_4431754, baseEnd_4431754] using wordTrace_append hprefix tailTrace_4431754
  have hstable : (prefixWord ++ tailWord_4431754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4431754).length < 2 ^ (prefixWord ++ tailWord_4431754).sum := by decide
  have hdescent : baseEnd_4431754 < baseStart_4431754 := by decide
  rcases family_descends (prefixWord ++ tailWord_4431754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4431770 : List Nat := [3, 1, 1, 4, 2, 2, 1, 2, 2, 3, 2]
def baseStart_4431770 : Nat := 118140960795 + 4431770 * 2 ^ 59
def prefixEnd_4431770 : Nat := 4983230072969 + 3 ^ 40 * 4431770 * 2
def baseEnd_4431770 : Nat := 2275628160176230913193667

theorem tailTrace_4431770 : CollatzResearch.WordTrace tailWord_4431770 prefixEnd_4431770 2275628160176230913193667 := by
  unfold tailWord_4431770
  simp only [CollatzResearch.WordTrace]
  refine ⟨40409982788615412725583191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107759954102974433934888509 40409982788615412725583191)
  ·
    refine ⟨60614974182923119088374787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40409982788615412725583191 60614974182923119088374787)
    ·
      refine ⟨90922461274384678632562181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60614974182923119088374787 90922461274384678632562181)
      ·
        refine ⟨17047961488947127243605409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90922461274384678632562181 17047961488947127243605409)
        ·
          refine ⟨12785971116710345432704057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17047961488947127243605409 12785971116710345432704057)
          ·
            refine ⟨9589478337532759074528043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12785971116710345432704057 9589478337532759074528043)
            ·
              refine ⟨14384217506299138611792065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9589478337532759074528043 14384217506299138611792065)
              ·
                refine ⟨10788163129724353958844049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14384217506299138611792065 10788163129724353958844049)
                ·
                  refine ⟨8091122347293265469133037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10788163129724353958844049 8091122347293265469133037)
                  ·
                    refine ⟨3034170880234974550924889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8091122347293265469133037 3034170880234974550924889)
                    ·
                      refine ⟨2275628160176230913193667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3034170880234974550924889 2275628160176230913193667)
                      ·
                        rfl

theorem cell23_4431770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_4431770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4431770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4431770 prefixEnd_4431770 := by exact prefixLift 4431770
  have htrace : WordTrace (prefixWord ++ tailWord_4431770) baseStart_4431770 baseEnd_4431770 := by
    simpa [prefixWord, tailWord_4431770, baseEnd_4431770] using wordTrace_append hprefix tailTrace_4431770
  have hstable : (prefixWord ++ tailWord_4431770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4431770).length < 2 ^ (prefixWord ++ tailWord_4431770).sum := by decide
  have hdescent : baseEnd_4431770 < baseStart_4431770 := by decide
  rcases family_descends (prefixWord ++ tailWord_4431770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4431777 : List Nat := [1, 2, 3, 4, 2, 2, 1, 1, 3, 1, 3]
def baseStart_4431777 : Nat := 118140960795 + 4431777 * 2 ^ 59
def prefixEnd_4431777 : Nat := 4983230072969 + 3 ^ 40 * 4431777 * 2
def baseEnd_4431777 : Nat := 2275631754540812385806135

theorem tailTrace_4431777 : CollatzResearch.WordTrace tailWord_4431777 prefixEnd_4431777 2275631754540812385806135 := by
  unfold tailWord_4431777
  simp only [CollatzResearch.WordTrace]
  refine ⟨161640186465436291097837585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107760124310290860731891723 161640186465436291097837585)
  ·
    refine ⟨121230139849077218323378189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161640186465436291097837585 121230139849077218323378189)
    ·
      refine ⟨45461302443403956871266821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121230139849077218323378189 45461302443403956871266821)
      ·
        refine ⟨8523994208138241913362529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45461302443403956871266821 8523994208138241913362529)
        ·
          refine ⟨6392995656103681435021897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8523994208138241913362529 6392995656103681435021897)
          ·
            refine ⟨4794746742077761076266423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6392995656103681435021897 4794746742077761076266423)
            ·
              refine ⟨7192120113116641614399635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4794746742077761076266423 7192120113116641614399635)
              ·
                refine ⟨10788180169674962421599453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7192120113116641614399635 10788180169674962421599453)
                ·
                  refine ⟨4045567563628110908099795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10788180169674962421599453 4045567563628110908099795)
                  ·
                    refine ⟨6068351345442166362149693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4045567563628110908099795 6068351345442166362149693)
                    ·
                      refine ⟨2275631754540812385806135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6068351345442166362149693 2275631754540812385806135)
                      ·
                        rfl

theorem cell23_4431777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_4431777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4431777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4431777 prefixEnd_4431777 := by exact prefixLift 4431777
  have htrace : WordTrace (prefixWord ++ tailWord_4431777) baseStart_4431777 baseEnd_4431777 := by
    simpa [prefixWord, tailWord_4431777, baseEnd_4431777] using wordTrace_append hprefix tailTrace_4431777
  have hstable : (prefixWord ++ tailWord_4431777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4431777).length < 2 ^ (prefixWord ++ tailWord_4431777).sum := by decide
  have hdescent : baseEnd_4431777 < baseStart_4431777 := by decide
  rcases family_descends (prefixWord ++ tailWord_4431777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4431784 : List Nat := [2, 1, 6, 2, 2, 1, 2, 1, 6]
def baseStart_4431784 : Nat := 118140960795 + 4431784 * 2 ^ 59
def prefixEnd_4431784 : Nat := 4983230072969 + 3 ^ 40 * 4431784 * 2
def baseEnd_4431784 : Nat := 252848372100599317602067

theorem tailTrace_4431784 : CollatzResearch.WordTrace tailWord_4431784 prefixEnd_4431784 252848372100599317602067 := by
  unfold tailWord_4431784
  simp only [CollatzResearch.WordTrace]
  refine ⟨80820220888205465646671203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107760294517607287528894937 80820220888205465646671203)
  ·
    refine ⟨121230331332308198470006805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80820220888205465646671203 121230331332308198470006805)
    ·
      refine ⟨5682671781201946803281569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 121230331332308198470006805 5682671781201946803281569)
      ·
        refine ⟨4262003835901460102461177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5682671781201946803281569 4262003835901460102461177)
        ·
          refine ⟨3196502876926095076845883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4262003835901460102461177 3196502876926095076845883)
          ·
            refine ⟨4794754315389142615268825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3196502876926095076845883 4794754315389142615268825)
            ·
              refine ⟨3596065736541856961451619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4794754315389142615268825 3596065736541856961451619)
              ·
                refine ⟨5394098604812785442177429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3596065736541856961451619 5394098604812785442177429)
                ·
                  refine ⟨252848372100599317602067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5394098604812785442177429 252848372100599317602067)
                  ·
                    rfl

theorem cell23_4431784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 2, 1, 6].length) (baseStart_4431784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4431784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4431784 prefixEnd_4431784 := by exact prefixLift 4431784
  have htrace : WordTrace (prefixWord ++ tailWord_4431784) baseStart_4431784 baseEnd_4431784 := by
    simpa [prefixWord, tailWord_4431784, baseEnd_4431784] using wordTrace_append hprefix tailTrace_4431784
  have hstable : (prefixWord ++ tailWord_4431784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4431784).length < 2 ^ (prefixWord ++ tailWord_4431784).sum := by decide
  have hdescent : baseEnd_4431784 < baseStart_4431784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4431784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4431806 : List Nat := [4, 2, 1, 1, 1, 3, 2, 9]
def baseStart_4431806 : Nat := 118140960795 + 4431806 * 2 ^ 59
def prefixEnd_4431806 : Nat := 4983230072969 + 3 ^ 40 * 4431806 * 2
def baseEnd_4431806 : Nat := 84283209091844176753463

theorem tailTrace_4431806 : CollatzResearch.WordTrace tailWord_4431806 prefixEnd_4431806 84283209091844176753463 := by
  unfold tailWord_4431806
  simp only [CollatzResearch.WordTrace]
  refine ⟨20205155522791403631330409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107760829454887486033762181 20205155522791403631330409)
  ·
    refine ⟨15153866642093552723497807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20205155522791403631330409 15153866642093552723497807)
    ·
      refine ⟨22730799963140329085246711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15153866642093552723497807 22730799963140329085246711)
      ·
        refine ⟨34096199944710493627870067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22730799963140329085246711 34096199944710493627870067)
        ·
          refine ⟨51144299917065740441805101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34096199944710493627870067 51144299917065740441805101)
          ·
            refine ⟨19179112468899652665676913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51144299917065740441805101 19179112468899652665676913)
            ·
              refine ⟨14384334351674739499257685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19179112468899652665676913 14384334351674739499257685)
              ·
                refine ⟨84283209091844176753463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14384334351674739499257685 84283209091844176753463)
                ·
                  rfl

theorem cell23_4431806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 9].length) (baseStart_4431806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4431806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4431806 prefixEnd_4431806 := by exact prefixLift 4431806
  have htrace : WordTrace (prefixWord ++ tailWord_4431806) baseStart_4431806 baseEnd_4431806 := by
    simpa [prefixWord, tailWord_4431806, baseEnd_4431806] using wordTrace_append hprefix tailTrace_4431806
  have hstable : (prefixWord ++ tailWord_4431806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4431806).length < 2 ^ (prefixWord ++ tailWord_4431806).sum := by decide
  have hdescent : baseEnd_4431806 < baseStart_4431806 := by decide
  rcases family_descends (prefixWord ++ tailWord_4431806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4431834 : List Nat := [3, 1, 1, 2, 5, 1, 1, 4, 1, 2, 2]
def baseStart_4431834 : Nat := 118140960795 + 4431834 * 2 ^ 59
def prefixEnd_4431834 : Nat := 4983230072969 + 3 ^ 40 * 4431834 * 2
def baseEnd_4431834 : Nat := 2275661022938118662793373

theorem tailTrace_4431834 : CollatzResearch.WordTrace tailWord_4431834 prefixEnd_4431834 2275661022938118662793373 := by
  unfold tailWord_4431834
  simp only [CollatzResearch.WordTrace]
  refine ⟨40410566356557447458165639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107761510284153193221775037 40410566356557447458165639)
  ·
    refine ⟨60615849534836171187248459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40410566356557447458165639 60615849534836171187248459)
    ·
      refine ⟨90923774302254256780872689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60615849534836171187248459 90923774302254256780872689)
      ·
        refine ⟨68192830726690692585654517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90923774302254256780872689 68192830726690692585654517)
        ·
          refine ⟨6393077880627252429905111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68192830726690692585654517 6393077880627252429905111)
          ·
            refine ⟨9589616820940878644857667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6393077880627252429905111 9589616820940878644857667)
            ·
              refine ⟨14384425231411317967286501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9589616820940878644857667 14384425231411317967286501)
              ·
                refine ⟨2697079730889622118866219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14384425231411317967286501 2697079730889622118866219)
                ·
                  refine ⟨4045619596334433178299329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2697079730889622118866219 4045619596334433178299329)
                  ·
                    refine ⟨3034214697250824883724497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4045619596334433178299329 3034214697250824883724497)
                    ·
                      refine ⟨2275661022938118662793373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3034214697250824883724497 2275661022938118662793373)
                      ·
                        rfl

theorem cell23_4431834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 4, 1, 2, 2].length) (baseStart_4431834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4431834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4431834 prefixEnd_4431834 := by exact prefixLift 4431834
  have htrace : WordTrace (prefixWord ++ tailWord_4431834) baseStart_4431834 baseEnd_4431834 := by
    simpa [prefixWord, tailWord_4431834, baseEnd_4431834] using wordTrace_append hprefix tailTrace_4431834
  have hstable : (prefixWord ++ tailWord_4431834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4431834).length < 2 ^ (prefixWord ++ tailWord_4431834).sum := by decide
  have hdescent : baseEnd_4431834 < baseStart_4431834 := by decide
  rcases family_descends (prefixWord ++ tailWord_4431834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4431850 : List Nat := [3, 1, 3, 1, 2, 1, 1, 5, 2, 1, 3]
def baseStart_4431850 : Nat := 118140960795 + 4431850 * 2 ^ 59
def prefixEnd_4431850 : Nat := 4983230072969 + 3 ^ 40 * 4431850 * 2
def baseEnd_4431850 : Nat := 2275669238628590600193299

theorem tailTrace_4431850 : CollatzResearch.WordTrace tailWord_4431850 prefixEnd_4431850 2275669238628590600193299 := by
  unfold tailWord_4431850
  simp only [CollatzResearch.WordTrace]
  refine ⟨40410712248542956141311251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107761899329447883043496669 40410712248542956141311251)
  ·
    refine ⟨60616068372814434211966877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40410712248542956141311251 60616068372814434211966877)
    ·
      refine ⟨22731025639805412829487579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60616068372814434211966877 22731025639805412829487579)
      ·
        refine ⟨34096538459708119244231369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22731025639805412829487579 34096538459708119244231369)
        ·
          refine ⟨25572403844781089433173527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34096538459708119244231369 25572403844781089433173527)
          ·
            refine ⟨38358605767171634149760291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25572403844781089433173527 38358605767171634149760291)
            ·
              refine ⟨57537908650757451224640437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38358605767171634149760291 57537908650757451224640437)
              ·
                refine ⟨5394178936008511052310041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57537908650757451224640437 5394178936008511052310041)
                ·
                  refine ⟨4045634202006383289232531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5394178936008511052310041 4045634202006383289232531)
                  ·
                    refine ⟨6068451303009574933848797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4045634202006383289232531 6068451303009574933848797)
                    ·
                      refine ⟨2275669238628590600193299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6068451303009574933848797 2275669238628590600193299)
                      ·
                        rfl

theorem cell23_4431850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 5, 2, 1, 3].length) (baseStart_4431850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4431850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4431850 prefixEnd_4431850 := by exact prefixLift 4431850
  have htrace : WordTrace (prefixWord ++ tailWord_4431850) baseStart_4431850 baseEnd_4431850 := by
    simpa [prefixWord, tailWord_4431850, baseEnd_4431850] using wordTrace_append hprefix tailTrace_4431850
  have hstable : (prefixWord ++ tailWord_4431850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4431850).length < 2 ^ (prefixWord ++ tailWord_4431850).sum := by decide
  have hdescent : baseEnd_4431850 < baseStart_4431850 := by decide
  rcases family_descends (prefixWord ++ tailWord_4431850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4431877 : List Nat := [1, 3, 1, 1, 2, 4, 4, 1, 1, 3, 2]
def baseStart_4431877 : Nat := 118140960795 + 4431877 * 2 ^ 59
def prefixEnd_4431877 : Nat := 4983230072969 + 3 ^ 40 * 4431877 * 2
def baseEnd_4431877 : Nat := 2275683102606261994555675

theorem tailTrace_4431877 : CollatzResearch.WordTrace tailWord_4431877 prefixEnd_4431877 2275683102606261994555675 := by
  unfold tailWord_4431877
  simp only [CollatzResearch.WordTrace]
  refine ⟨161643833765074008176477885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107762555843382672117651923 161643833765074008176477885)
  ·
    refine ⟨60616437661902753066179207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161643833765074008176477885 60616437661902753066179207)
    ·
      refine ⟨90924656492854129599268811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60616437661902753066179207 90924656492854129599268811)
      ·
        refine ⟨136386984739281194398903217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90924656492854129599268811 136386984739281194398903217)
        ·
          refine ⟨102290238554460895799177413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136386984739281194398903217 102290238554460895799177413)
          ·
            refine ⟨19179419728961417962345765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 102290238554460895799177413 19179419728961417962345765)
            ·
              refine ⟨3596141199180265867939831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19179419728961417962345765 3596141199180265867939831)
              ·
                refine ⟨5394211798770398801909747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3596141199180265867939831 5394211798770398801909747)
                ·
                  refine ⟨8091317698155598202864621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5394211798770398801909747 8091317698155598202864621)
                  ·
                    refine ⟨3034244136808349326074233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8091317698155598202864621 3034244136808349326074233)
                    ·
                      refine ⟨2275683102606261994555675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3034244136808349326074233 2275683102606261994555675)
                      ·
                        rfl

theorem cell23_4431877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4, 1, 1, 3, 2].length) (baseStart_4431877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4431877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4431877 prefixEnd_4431877 := by exact prefixLift 4431877
  have htrace : WordTrace (prefixWord ++ tailWord_4431877) baseStart_4431877 baseEnd_4431877 := by
    simpa [prefixWord, tailWord_4431877, baseEnd_4431877] using wordTrace_append hprefix tailTrace_4431877
  have hstable : (prefixWord ++ tailWord_4431877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4431877).length < 2 ^ (prefixWord ++ tailWord_4431877).sum := by decide
  have hdescent : baseEnd_4431877 < baseStart_4431877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4431877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4431878 : List Nat := [6, 2, 1, 2, 1, 2, 1, 2, 2, 4]
def baseStart_4431878 : Nat := 118140960795 + 4431878 * 2 ^ 59
def prefixEnd_4431878 : Nat := 4983230072969 + 3 ^ 40 * 4431878 * 2
def baseEnd_4431878 : Nat := 758561205362305496881057

theorem tailTrace_4431878 : CollatzResearch.WordTrace tailWord_4431878 prefixEnd_4431878 758561205362305496881057 := by
  unfold tailWord_4431878
  simp only [CollatzResearch.WordTrace]
  refine ⟨5051370944939699542102009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 107762580158713590231509525 5051370944939699542102009)
  ·
    refine ⟨3788528208704774656576507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5051370944939699542102009 3788528208704774656576507)
    ·
      refine ⟨5682792313057161984864761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3788528208704774656576507 5682792313057161984864761)
      ·
        refine ⟨4262094234792871488648571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5682792313057161984864761 4262094234792871488648571)
        ·
          refine ⟨6393141352189307232972857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4262094234792871488648571 6393141352189307232972857)
          ·
            refine ⟨4794856014141980424729643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6393141352189307232972857 4794856014141980424729643)
            ·
              refine ⟨7192284021212970637094465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4794856014141980424729643 7192284021212970637094465)
              ·
                refine ⟨5394213015909727977820849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7192284021212970637094465 5394213015909727977820849)
                ·
                  refine ⟨4045659761932295983365637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5394213015909727977820849 4045659761932295983365637)
                  ·
                    refine ⟨758561205362305496881057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4045659761932295983365637 758561205362305496881057)
                    ·
                      rfl

theorem cell23_4431878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_4431878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4431878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4431878 prefixEnd_4431878 := by exact prefixLift 4431878
  have htrace : WordTrace (prefixWord ++ tailWord_4431878) baseStart_4431878 baseEnd_4431878 := by
    simpa [prefixWord, tailWord_4431878, baseEnd_4431878] using wordTrace_append hprefix tailTrace_4431878
  have hstable : (prefixWord ++ tailWord_4431878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4431878).length < 2 ^ (prefixWord ++ tailWord_4431878).sum := by decide
  have hdescent : baseEnd_4431878 < baseStart_4431878 := by decide
  rcases family_descends (prefixWord ++ tailWord_4431878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4431943 : List Nat := [1, 1, 4, 1, 3, 1, 3, 2, 2, 5]
def baseStart_4431943 : Nat := 118140960795 + 4431943 * 2 ^ 59
def prefixEnd_4431943 : Nat := 4983230072969 + 3 ^ 40 * 4431943 * 2
def baseEnd_4431943 : Nat := 758572330776486245443457

theorem tailTrace_4431943 : CollatzResearch.WordTrace tailWord_4431943 prefixEnd_4431943 758572330776486245443457 := by
  unfold tailWord_4431943
  simp only [CollatzResearch.WordTrace]
  refine ⟨161646240982834901448380483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107764160655223267632253655 161646240982834901448380483)
  ·
    refine ⟨242469361474252352172570725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161646240982834901448380483 242469361474252352172570725)
    ·
      refine ⟨45463005276422316032357011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 242469361474252352172570725 45463005276422316032357011)
      ·
        refine ⟨68194507914633474048535517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45463005276422316032357011 68194507914633474048535517)
        ·
          refine ⟨25572940467987552768200819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68194507914633474048535517 25572940467987552768200819)
          ·
            refine ⟨38359410701981329152301229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25572940467987552768200819 38359410701981329152301229)
            ·
              refine ⟨14384779013242998432112961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38359410701981329152301229 14384779013242998432112961)
              ·
                refine ⟨10788584259932248824084721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14384779013242998432112961 10788584259932248824084721)
                ·
                  refine ⟨8091438194949186618063541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10788584259932248824084721 8091438194949186618063541)
                  ·
                    refine ⟨758572330776486245443457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8091438194949186618063541 758572330776486245443457)
                    ·
                      rfl

theorem cell23_4431943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 2, 2, 5].length) (baseStart_4431943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4431943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4431943 prefixEnd_4431943 := by exact prefixLift 4431943
  have htrace : WordTrace (prefixWord ++ tailWord_4431943) baseStart_4431943 baseEnd_4431943 := by
    simpa [prefixWord, tailWord_4431943, baseEnd_4431943] using wordTrace_append hprefix tailTrace_4431943
  have hstable : (prefixWord ++ tailWord_4431943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4431943).length < 2 ^ (prefixWord ++ tailWord_4431943).sum := by decide
  have hdescent : baseEnd_4431943 < baseStart_4431943 := by decide
  rcases family_descends (prefixWord ++ tailWord_4431943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4431958 : List Nat := [5, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2]
def baseStart_4431958 : Nat := 118140960795 + 4431958 * 2 ^ 59
def prefixEnd_4431958 : Nat := 4983230072969 + 3 ^ 40 * 4431958 * 2
def baseEnd_4431958 : Nat := 2275724694539276177642803

theorem tailTrace_4431958 : CollatzResearch.WordTrace tailWord_4431958 prefixEnd_4431958 2275724694539276177642803 := by
  unfold tailWord_4431958
  simp only [CollatzResearch.WordTrace]
  refine ⟨10102924254861284938136033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 107764525385187039340117685 10102924254861284938136033)
  ·
    refine ⟨7577193191145963703602025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10102924254861284938136033 7577193191145963703602025)
    ·
      refine ⟨5682894893359472777701519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7577193191145963703602025 5682894893359472777701519)
      ·
        refine ⟨8524342340039209166552279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5682894893359472777701519 8524342340039209166552279)
        ·
          refine ⟨12786513510058813749828419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8524342340039209166552279 12786513510058813749828419)
          ·
            refine ⟨19179770265088220624742629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12786513510058813749828419 19179770265088220624742629)
            ·
              refine ⟨3596206924704041367139243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19179770265088220624742629 3596206924704041367139243)
              ·
                refine ⟨5394310387056062050708865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3596206924704041367139243 5394310387056062050708865)
                ·
                  refine ⟨4045732790292046538031649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5394310387056062050708865 4045732790292046538031649)
                  ·
                    refine ⟨3034299592719034903523737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4045732790292046538031649 3034299592719034903523737)
                    ·
                      refine ⟨2275724694539276177642803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3034299592719034903523737 2275724694539276177642803)
                      ·
                        rfl

theorem cell23_4431958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_4431958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4431958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4431958 prefixEnd_4431958 := by exact prefixLift 4431958
  have htrace : WordTrace (prefixWord ++ tailWord_4431958) baseStart_4431958 baseEnd_4431958 := by
    simpa [prefixWord, tailWord_4431958, baseEnd_4431958] using wordTrace_append hprefix tailTrace_4431958
  have hstable : (prefixWord ++ tailWord_4431958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4431958).length < 2 ^ (prefixWord ++ tailWord_4431958).sum := by decide
  have hdescent : baseEnd_4431958 < baseStart_4431958 := by decide
  rcases family_descends (prefixWord ++ tailWord_4431958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4431980 : List Nat := [2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 4]
def baseStart_4431980 : Nat := 118140960795 + 4431980 * 2 ^ 59
def prefixEnd_4431980 : Nat := 4983230072969 + 3 ^ 40 * 4431980 * 2
def baseEnd_4431980 : Nat := 2275735991113675091567701

theorem tailTrace_4431980 : CollatzResearch.WordTrace tailWord_4431980 prefixEnd_4431980 2275735991113675091567701 := by
  unfold tailWord_4431980
  simp only [CollatzResearch.WordTrace]
  refine ⟨80823795241850428383738697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107765060322467237844984929 80823795241850428383738697)
  ·
    refine ⟨60617846431387821287804023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80823795241850428383738697 60617846431387821287804023)
    ·
      refine ⟨90926769647081731931706035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60617846431387821287804023 90926769647081731931706035)
      ·
        refine ⟨136390154470622597897559053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90926769647081731931706035 136390154470622597897559053)
        ·
          refine ⟨51146307926483474211584645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136390154470622597897559053 51146307926483474211584645)
          ·
            refine ⟨9589932736215651414672121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51146307926483474211584645 9589932736215651414672121)
            ·
              refine ⟨7192449552161738561004091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9589932736215651414672121 7192449552161738561004091)
              ·
                refine ⟨10788674328242607841506137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7192449552161738561004091 10788674328242607841506137)
                ·
                  refine ⟨8091505746181955881129603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10788674328242607841506137 8091505746181955881129603)
                  ·
                    refine ⟨12137258619272933821694405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8091505746181955881129603 12137258619272933821694405)
                    ·
                      refine ⟨2275735991113675091567701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12137258619272933821694405 2275735991113675091567701)
                      ·
                        rfl

theorem cell23_4431980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 4].length) (baseStart_4431980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4431980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4431980 prefixEnd_4431980 := by exact prefixLift 4431980
  have htrace : WordTrace (prefixWord ++ tailWord_4431980) baseStart_4431980 baseEnd_4431980 := by
    simpa [prefixWord, tailWord_4431980, baseEnd_4431980] using wordTrace_append hprefix tailTrace_4431980
  have hstable : (prefixWord ++ tailWord_4431980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4431980).length < 2 ^ (prefixWord ++ tailWord_4431980).sum := by decide
  have hdescent : baseEnd_4431980 < baseStart_4431980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4431980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4432003 : List Nat := [1, 1, 1, 3, 3, 3, 1, 4, 6]
def baseStart_4432003 : Nat := 118140960795 + 4432003 * 2 ^ 59
def prefixEnd_4432003 : Nat := 4983230072969 + 3 ^ 40 * 4432003 * 2
def baseEnd_4432003 : Nat := 252860866796525389064455

theorem tailTrace_4432003 : CollatzResearch.WordTrace tailWord_4432003 prefixEnd_4432003 252860866796525389064455 := by
  unfold tailWord_4432003
  simp only [CollatzResearch.WordTrace]
  refine ⟨161648429362617531695564663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107765619575078354463709775 161648429362617531695564663)
  ·
    refine ⟨242472644043926297543346995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161648429362617531695564663 242472644043926297543346995)
    ·
      refine ⟨363708966065889446315020493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242472644043926297543346995 363708966065889446315020493)
      ·
        refine ⟨136390862274708542368132685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 363708966065889446315020493 136390862274708542368132685)
        ·
          refine ⟨51146573353015703388049757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136390862274708542368132685 51146573353015703388049757)
          ·
            refine ⟨19179965007380888770518659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51146573353015703388049757 19179965007380888770518659)
            ·
              refine ⟨28769947511071333155777989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19179965007380888770518659 28769947511071333155777989)
              ·
                refine ⟨5394365158325874966708373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28769947511071333155777989 5394365158325874966708373)
                ·
                  refine ⟨252860866796525389064455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5394365158325874966708373 252860866796525389064455)
                  ·
                    rfl

theorem cell23_4432003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 4, 6].length) (baseStart_4432003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4432003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4432003 prefixEnd_4432003 := by exact prefixLift 4432003
  have htrace : WordTrace (prefixWord ++ tailWord_4432003) baseStart_4432003 baseEnd_4432003 := by
    simpa [prefixWord, tailWord_4432003, baseEnd_4432003] using wordTrace_append hprefix tailTrace_4432003
  have hstable : (prefixWord ++ tailWord_4432003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4432003).length < 2 ^ (prefixWord ++ tailWord_4432003).sum := by decide
  have hdescent : baseEnd_4432003 < baseStart_4432003 := by decide
  rcases family_descends (prefixWord ++ tailWord_4432003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4432034 : List Nat := [3, 3, 1, 3, 1, 3, 1, 1, 2, 2, 3]
def baseStart_4432034 : Nat := 118140960795 + 4432034 * 2 ^ 59
def prefixEnd_4432034 : Nat := 4983230072969 + 3 ^ 40 * 4432034 * 2
def baseEnd_4432034 : Nat := 2275763719069017880292453

theorem tailTrace_4432034 : CollatzResearch.WordTrace tailWord_4432034 prefixEnd_4432034 2275763719069017880292453 := by
  unfold tailWord_4432034
  simp only [CollatzResearch.WordTrace]
  refine ⟨40412390006376305997485789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107766373350336815993295437 40412390006376305997485789)
  ·
    refine ⟨15154646252391114749057171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40412390006376305997485789 15154646252391114749057171)
    ·
      refine ⟨22731969378586672123585757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15154646252391114749057171 22731969378586672123585757)
      ·
        refine ⟨8524488516970002046344659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22731969378586672123585757 8524488516970002046344659)
        ·
          refine ⟨12786732775455003069516989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8524488516970002046344659 12786732775455003069516989)
          ·
            refine ⟨4795024790795626151068871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12786732775455003069516989 4795024790795626151068871)
            ·
              refine ⟨7192537186193439226603307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4795024790795626151068871 7192537186193439226603307)
              ·
                refine ⟨10788805779290158839904961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7192537186193439226603307 10788805779290158839904961)
                ·
                  refine ⟨8091604334467619129928721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10788805779290158839904961 8091604334467619129928721)
                  ·
                    refine ⟨6068703250850714347446541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8091604334467619129928721 6068703250850714347446541)
                    ·
                      refine ⟨2275763719069017880292453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6068703250850714347446541 2275763719069017880292453)
                      ·
                        rfl

theorem cell23_4432034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_4432034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4432034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4432034 prefixEnd_4432034 := by exact prefixLift 4432034
  have htrace : WordTrace (prefixWord ++ tailWord_4432034) baseStart_4432034 baseEnd_4432034 := by
    simpa [prefixWord, tailWord_4432034, baseEnd_4432034] using wordTrace_append hprefix tailTrace_4432034
  have hstable : (prefixWord ++ tailWord_4432034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4432034).length < 2 ^ (prefixWord ++ tailWord_4432034).sum := by decide
  have hdescent : baseEnd_4432034 < baseStart_4432034 := by decide
  rcases family_descends (prefixWord ++ tailWord_4432034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4432050 : List Nat := [3, 2, 1, 1, 1, 3, 3, 3, 1, 5]
def baseStart_4432050 : Nat := 118140960795 + 4432050 * 2 ^ 59
def prefixEnd_4432050 : Nat := 4983230072969 + 3 ^ 40 * 4432050 * 2
def baseEnd_4432050 : Nat := 758590644919829939230793

theorem tailTrace_4432050 : CollatzResearch.WordTrace tailWord_4432050 prefixEnd_4432050 758590644919829939230793 := by
  unfold tailWord_4432050
  simp only [CollatzResearch.WordTrace]
  refine ⟨40412535898361814680631401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107766762395631505815017069 40412535898361814680631401)
  ·
    refine ⟨30309401923771361010473551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40412535898361814680631401 30309401923771361010473551)
    ·
      refine ⟨45464102885657041515710327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30309401923771361010473551 45464102885657041515710327)
      ·
        refine ⟨68196154328485562273565491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45464102885657041515710327 68196154328485562273565491)
        ·
          refine ⟨102294231492728343410348237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68196154328485562273565491 102294231492728343410348237)
          ·
            refine ⟨38360336809773128778880589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102294231492728343410348237 38360336809773128778880589)
            ·
              refine ⟨14385126303664923292080221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38360336809773128778880589 14385126303664923292080221)
              ·
                refine ⟨5394422363874346234530083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14385126303664923292080221 5394422363874346234530083)
                ·
                  refine ⟨8091633545811519351795125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5394422363874346234530083 8091633545811519351795125)
                  ·
                    refine ⟨758590644919829939230793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8091633545811519351795125 758590644919829939230793)
                    ·
                      rfl

theorem cell23_4432050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 3, 1, 5].length) (baseStart_4432050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4432050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4432050 prefixEnd_4432050 := by exact prefixLift 4432050
  have htrace : WordTrace (prefixWord ++ tailWord_4432050) baseStart_4432050 baseEnd_4432050 := by
    simpa [prefixWord, tailWord_4432050, baseEnd_4432050] using wordTrace_append hprefix tailTrace_4432050
  have hstable : (prefixWord ++ tailWord_4432050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4432050).length < 2 ^ (prefixWord ++ tailWord_4432050).sum := by decide
  have hdescent : baseEnd_4432050 < baseStart_4432050 := by decide
  rcases family_descends (prefixWord ++ tailWord_4432050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4432064 : List Nat := [2, 1, 1, 2, 5, 1, 2, 4, 1, 1, 3]
def baseStart_4432064 : Nat := 118140960795 + 4432064 * 2 ^ 59
def prefixEnd_4432064 : Nat := 4983230072969 + 3 ^ 40 * 4432064 * 2
def baseEnd_4432064 : Nat := 2275779123488652762917315

theorem tailTrace_4432064 : CollatzResearch.WordTrace tailWord_4432064 prefixEnd_4432064 2275779123488652762917315 := by
  unfold tailWord_4432064
  simp only [CollatzResearch.WordTrace]
  refine ⟨80825327107698269556767623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107767102810264359409023497 80825327107698269556767623)
  ·
    refine ⟨121237990661547404335151435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80825327107698269556767623 121237990661547404335151435)
    ·
      refine ⟨181856985992321106502727153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121237990661547404335151435 181856985992321106502727153)
      ·
        refine ⟨136392739494240829877045365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181856985992321106502727153 136392739494240829877045365)
        ·
          refine ⟨12786819327585077800973003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 136392739494240829877045365 12786819327585077800973003)
          ·
            refine ⟨19180228991377616701459505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12786819327585077800973003 19180228991377616701459505)
            ·
              refine ⟨14385171743533212526094629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19180228991377616701459505 14385171743533212526094629)
              ·
                refine ⟨2697219701912477348642743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14385171743533212526094629 2697219701912477348642743)
                ·
                  refine ⟨4045829552868716022964115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2697219701912477348642743 4045829552868716022964115)
                  ·
                    refine ⟨6068744329303074034446173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4045829552868716022964115 6068744329303074034446173)
                    ·
                      refine ⟨2275779123488652762917315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6068744329303074034446173 2275779123488652762917315)
                      ·
                        rfl

theorem cell23_4432064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 4, 1, 1, 3].length) (baseStart_4432064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4432064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4432064 prefixEnd_4432064 := by exact prefixLift 4432064
  have htrace : WordTrace (prefixWord ++ tailWord_4432064) baseStart_4432064 baseEnd_4432064 := by
    simpa [prefixWord, tailWord_4432064, baseEnd_4432064] using wordTrace_append hprefix tailTrace_4432064
  have hstable : (prefixWord ++ tailWord_4432064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4432064).length < 2 ^ (prefixWord ++ tailWord_4432064).sum := by decide
  have hdescent : baseEnd_4432064 < baseStart_4432064 := by decide
  rcases family_descends (prefixWord ++ tailWord_4432064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4432073 : List Nat := [1, 2, 1, 1, 2, 1, 1, 3, 2, 6, 3]
def baseStart_4432073 : Nat := 118140960795 + 4432073 * 2 ^ 59
def prefixEnd_4432073 : Nat := 4983230072969 + 3 ^ 40 * 4432073 * 2
def baseEnd_4432073 : Nat := 2275783744814543227704773

theorem tailTrace_4432073 : CollatzResearch.WordTrace tailWord_4432073 prefixEnd_4432073 2275783744814543227704773 := by
  unfold tailWord_4432073
  simp only [CollatzResearch.WordTrace]
  refine ⟨161650982472363933650612873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107767321648242622433741915 161650982472363933650612873)
  ·
    refine ⟨121238236854272950237959655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161650982472363933650612873 121238236854272950237959655)
    ·
      refine ⟨181857355281409425356939483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121238236854272950237959655 181857355281409425356939483)
      ·
        refine ⟨272786032922114138035409225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181857355281409425356939483 272786032922114138035409225)
        ·
          refine ⟨204589524691585603526556919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 272786032922114138035409225 204589524691585603526556919)
          ·
            refine ⟨306884287037378405289835379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204589524691585603526556919 306884287037378405289835379)
            ·
              refine ⟨460326430556067607934753069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 306884287037378405289835379 460326430556067607934753069)
              ·
                refine ⟨172622411458525352975532401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 460326430556067607934753069 172622411458525352975532401)
                ·
                  refine ⟨129466808593894014731649301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 172622411458525352975532401 129466808593894014731649301)
                  ·
                    refine ⟨6068756652838781940546061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 129466808593894014731649301 6068756652838781940546061)
                    ·
                      refine ⟨2275783744814543227704773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6068756652838781940546061 2275783744814543227704773)
                      ·
                        rfl

theorem cell23_4432073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 6, 3].length) (baseStart_4432073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4432073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4432073 prefixEnd_4432073 := by exact prefixLift 4432073
  have htrace : WordTrace (prefixWord ++ tailWord_4432073) baseStart_4432073 baseEnd_4432073 := by
    simpa [prefixWord, tailWord_4432073, baseEnd_4432073] using wordTrace_append hprefix tailTrace_4432073
  have hstable : (prefixWord ++ tailWord_4432073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4432073).length < 2 ^ (prefixWord ++ tailWord_4432073).sum := by decide
  have hdescent : baseEnd_4432073 < baseStart_4432073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4432073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4432090 : List Nat := [3, 1, 1, 2, 2, 1, 2, 3, 3, 2, 3]
def baseStart_4432090 : Nat := 118140960795 + 4432090 * 2 ^ 59
def prefixEnd_4432090 : Nat := 4983230072969 + 3 ^ 40 * 4432090 * 2
def baseEnd_4432090 : Nat := 2275792473985669661192195

theorem tailTrace_4432090 : CollatzResearch.WordTrace tailWord_4432090 prefixEnd_4432090 2275792473985669661192195 := by
  unfold tailWord_4432090
  simp only [CollatzResearch.WordTrace]
  refine ⟨40412900628325586388495431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107767735008868230369321149 40412900628325586388495431)
  ·
    refine ⟨60619350942488379582743147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40412900628325586388495431 60619350942488379582743147)
    ·
      refine ⟨90929026413732569374114721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60619350942488379582743147 90929026413732569374114721)
      ·
        refine ⟨68196769810299427030586041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90929026413732569374114721 68196769810299427030586041)
        ·
          refine ⟨51147577357724570272939531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68196769810299427030586041 51147577357724570272939531)
          ·
            refine ⟨76721366036586855409409297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51147577357724570272939531 76721366036586855409409297)
            ·
              refine ⟨57541024527440141557056973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76721366036586855409409297 57541024527440141557056973)
              ·
                refine ⟨21577884197790053083896365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57541024527440141557056973 21577884197790053083896365)
                ·
                  refine ⟨8091706574171269906461137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21577884197790053083896365 8091706574171269906461137)
                  ·
                    refine ⟨6068779930628452429845853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8091706574171269906461137 6068779930628452429845853)
                    ·
                      refine ⟨2275792473985669661192195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6068779930628452429845853 2275792473985669661192195)
                      ·
                        rfl

theorem cell23_4432090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 3, 2, 3].length) (baseStart_4432090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4432090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4432090 prefixEnd_4432090 := by exact prefixLift 4432090
  have htrace : WordTrace (prefixWord ++ tailWord_4432090) baseStart_4432090 baseEnd_4432090 := by
    simpa [prefixWord, tailWord_4432090, baseEnd_4432090] using wordTrace_append hprefix tailTrace_4432090
  have hstable : (prefixWord ++ tailWord_4432090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4432090).length < 2 ^ (prefixWord ++ tailWord_4432090).sum := by decide
  have hdescent : baseEnd_4432090 < baseStart_4432090 := by decide
  rcases family_descends (prefixWord ++ tailWord_4432090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4432133 : List Nat := [1, 3, 1, 1, 2, 1, 2, 2, 1, 4, 5]
def baseStart_4432133 : Nat := 118140960795 + 4432133 * 2 ^ 59
def prefixEnd_4432133 : Nat := 4983230072969 + 3 ^ 40 * 4432133 * 2
def baseEnd_4432133 : Nat := 2275814553653812992954497

theorem tailTrace_4432133 : CollatzResearch.WordTrace tailWord_4432133 prefixEnd_4432133 2275814553653812992954497 := by
  unfold tailWord_4432133
  simp only [CollatzResearch.WordTrace]
  refine ⟨161653170852146563897797053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107768780568097709265198035 161653170852146563897797053)
  ·
    refine ⟨60619939069554961461673895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161653170852146563897797053 60619939069554961461673895)
    ·
      refine ⟨90929908604332442192510843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60619939069554961461673895 90929908604332442192510843)
      ·
        refine ⟨136394862906498663288766265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90929908604332442192510843 136394862906498663288766265)
        ·
          refine ⟨102296147179873997466574699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136394862906498663288766265 102296147179873997466574699)
          ·
            refine ⟨153444220769810996199862049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102296147179873997466574699 153444220769810996199862049)
            ·
              refine ⟨115083165577358247149896537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 153444220769810996199862049 115083165577358247149896537)
              ·
                refine ⟨86312374183018685362422403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115083165577358247149896537 86312374183018685362422403)
                ·
                  refine ⟨129468561274528028043633605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86312374183018685362422403 129468561274528028043633605)
                  ·
                    refine ⟨24275355238974005258181301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 129468561274528028043633605 24275355238974005258181301)
                    ·
                      refine ⟨2275814553653812992954497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24275355238974005258181301 2275814553653812992954497)
                      ·
                        rfl

theorem cell23_4432133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 4, 5].length) (baseStart_4432133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4432133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4432133 prefixEnd_4432133 := by exact prefixLift 4432133
  have htrace : WordTrace (prefixWord ++ tailWord_4432133) baseStart_4432133 baseEnd_4432133 := by
    simpa [prefixWord, tailWord_4432133, baseEnd_4432133] using wordTrace_append hprefix tailTrace_4432133
  have hstable : (prefixWord ++ tailWord_4432133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4432133).length < 2 ^ (prefixWord ++ tailWord_4432133).sum := by decide
  have hdescent : baseEnd_4432133 < baseStart_4432133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4432133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4432158 : List Nat := [4, 3, 2, 1, 1, 2, 3, 1, 1, 2, 3]
def baseStart_4432158 : Nat := 118140960795 + 4432158 * 2 ^ 59
def prefixEnd_4432158 : Nat := 4983230072969 + 3 ^ 40 * 4432158 * 2
def baseEnd_4432158 : Nat := 2275827390670175395141883

theorem tailTrace_4432158 : CollatzResearch.WordTrace tailWord_4432158 prefixEnd_4432158 2275827390670175395141883 := by
  unfold tailWord_4432158
  simp only [CollatzResearch.WordTrace]
  refine ⟨20206760334631999145932141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107769388451370662111638085 20206760334631999145932141)
  ·
    refine ⟨7577535125486999679724553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20206760334631999145932141 7577535125486999679724553)
    ·
      refine ⟨5683151344115249759793415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7577535125486999679724553 5683151344115249759793415)
      ·
        refine ⟨8524727016172874639690123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5683151344115249759793415 8524727016172874639690123)
        ·
          refine ⟨12787090524259311959535185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8524727016172874639690123 12787090524259311959535185)
          ·
            refine ⟨9590317893194483969651389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12787090524259311959535185 9590317893194483969651389)
            ·
              refine ⟨3596369209947931488619271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9590317893194483969651389 3596369209947931488619271)
              ·
                refine ⟨5394553814921897232928907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3596369209947931488619271 5394553814921897232928907)
                ·
                  refine ⟨8091830722382845849393361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5394553814921897232928907 8091830722382845849393361)
                  ·
                    refine ⟨6068873041787134387045021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8091830722382845849393361 6068873041787134387045021)
                    ·
                      refine ⟨2275827390670175395141883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6068873041787134387045021 2275827390670175395141883)
                      ·
                        rfl

theorem cell23_4432158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_4432158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4432158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4432158 prefixEnd_4432158 := by exact prefixLift 4432158
  have htrace : WordTrace (prefixWord ++ tailWord_4432158) baseStart_4432158 baseEnd_4432158 := by
    simpa [prefixWord, tailWord_4432158, baseEnd_4432158] using wordTrace_append hprefix tailTrace_4432158
  have hstable : (prefixWord ++ tailWord_4432158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4432158).length < 2 ^ (prefixWord ++ tailWord_4432158).sum := by decide
  have hdescent : baseEnd_4432158 < baseStart_4432158 := by decide
  rcases family_descends (prefixWord ++ tailWord_4432158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4432183 : List Nat := [1, 1, 3, 1, 2, 1, 1, 2, 11]
def baseStart_4432183 : Nat := 118140960795 + 4432183 * 2 ^ 59
def prefixEnd_4432183 : Nat := 4983230072969 + 3 ^ 40 * 4432183 * 2
def baseEnd_4432183 : Nat := 252871136409615310814363

theorem tailTrace_4432183 : CollatzResearch.WordTrace tailWord_4432183 prefixEnd_4432183 252871136409615310814363 := by
  unfold tailWord_4432183
  simp only [CollatzResearch.WordTrace]
  refine ⟨161654994501965422437117203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107769996334643614958078135 161654994501965422437117203)
  ·
    refine ⟨242482491752948133655675805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161654994501965422437117203 242482491752948133655675805)
    ·
      refine ⟨90930934407355550120878427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 242482491752948133655675805 90930934407355550120878427)
      ·
        refine ⟨136396401611033325181317641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90930934407355550120878427 136396401611033325181317641)
        ·
          refine ⟨102297301208274993885988231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136396401611033325181317641 102297301208274993885988231)
          ·
            refine ⟨153445951812412490828982347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102297301208274993885988231 153445951812412490828982347)
            ·
              refine ⟨230168927718618736243473521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153445951812412490828982347 230168927718618736243473521)
              ·
                refine ⟨172626695788964052182605141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 230168927718618736243473521 172626695788964052182605141)
                ·
                  refine ⟨252871136409615310814363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 172626695788964052182605141 252871136409615310814363)
                  ·
                    rfl

theorem cell23_4432183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 11].length) (baseStart_4432183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4432183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4432183 prefixEnd_4432183 := by exact prefixLift 4432183
  have htrace : WordTrace (prefixWord ++ tailWord_4432183) baseStart_4432183 baseEnd_4432183 := by
    simpa [prefixWord, tailWord_4432183, baseEnd_4432183] using wordTrace_append hprefix tailTrace_4432183
  have hstable : (prefixWord ++ tailWord_4432183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4432183).length < 2 ^ (prefixWord ++ tailWord_4432183).sum := by decide
  have hdescent : baseEnd_4432183 < baseStart_4432183 := by decide
  rcases family_descends (prefixWord ++ tailWord_4432183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4432234 : List Nat := [3, 1, 3, 3, 1, 1, 2, 4, 5]
def baseStart_4432234 : Nat := 118140960795 + 4432234 * 2 ^ 59
def prefixEnd_4432234 : Nat := 4983230072969 + 3 ^ 40 * 4432234 * 2
def baseEnd_4432234 : Nat := 252874046133324121976837

theorem tailTrace_4432234 : CollatzResearch.WordTrace tailWord_4432234 prefixEnd_4432234 252874046133324121976837 := by
  unfold tailWord_4432234
  simp only [CollatzResearch.WordTrace]
  refine ⟨40414213656195164536805939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107771236416520438764815837 40414213656195164536805939)
  ·
    refine ⟨60621320484292746805208909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40414213656195164536805939 60621320484292746805208909)
    ·
      refine ⟨22732995181609780051953341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60621320484292746805208909 22732995181609780051953341)
      ·
        refine ⟨8524873193103667519482503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22732995181609780051953341 8524873193103667519482503)
        ·
          refine ⟨12787309789655501279223755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8524873193103667519482503 12787309789655501279223755)
          ·
            refine ⟨19180964684483251918835633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12787309789655501279223755 19180964684483251918835633)
            ·
              refine ⟨14385723513362438939126725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19180964684483251918835633 14385723513362438939126725)
              ·
                refine ⟨2697323158755457301086261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14385723513362438939126725 2697323158755457301086261)
                ·
                  refine ⟨252874046133324121976837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2697323158755457301086261 252874046133324121976837)
                  ·
                    rfl

theorem cell23_4432234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 4, 5].length) (baseStart_4432234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4432234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4432234 prefixEnd_4432234 := by exact prefixLift 4432234
  have htrace : WordTrace (prefixWord ++ tailWord_4432234) baseStart_4432234 baseEnd_4432234 := by
    simpa [prefixWord, tailWord_4432234, baseEnd_4432234] using wordTrace_append hprefix tailTrace_4432234
  have hstable : (prefixWord ++ tailWord_4432234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4432234).length < 2 ^ (prefixWord ++ tailWord_4432234).sum := by decide
  have hdescent : baseEnd_4432234 < baseStart_4432234 := by decide
  rcases family_descends (prefixWord ++ tailWord_4432234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4432260 : List Nat := [2, 3, 2, 1, 1, 2, 1, 1, 2, 8]
def baseStart_4432260 : Nat := 118140960795 + 4432260 * 2 ^ 59
def prefixEnd_4432260 : Nat := 4983230072969 + 3 ^ 40 * 4432260 * 2
def baseEnd_4432260 : Nat := 758626588565644665355471

theorem tailTrace_4432260 : CollatzResearch.WordTrace tailWord_4432260 prefixEnd_4432260 758626588565644665355471 := by
  unfold tailWord_4432260
  simp only [CollatzResearch.WordTrace]
  refine ⟨80828901461343232293835117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107771868615124309725113489 80828901461343232293835117)
  ·
    refine ⟨30310838048003712110188169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80828901461343232293835117 30310838048003712110188169)
    ·
      refine ⟨22733128536002784082641127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30310838048003712110188169 22733128536002784082641127)
      ·
        refine ⟨34099692804004176123961691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22733128536002784082641127 34099692804004176123961691)
        ·
          refine ⟨51149539206006264185942537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34099692804004176123961691 51149539206006264185942537)
          ·
            refine ⟨38362154404504698139456903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51149539206006264185942537 38362154404504698139456903)
            ·
              refine ⟨57543231606757047209185355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38362154404504698139456903 57543231606757047209185355)
              ·
                refine ⟨86314847410135570813778033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57543231606757047209185355 86314847410135570813778033)
                ·
                  refine ⟨64736135557601678110333525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86314847410135570813778033 64736135557601678110333525)
                  ·
                    refine ⟨758626588565644665355471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 64736135557601678110333525 758626588565644665355471)
                    ·
                      rfl

theorem cell23_4432260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_4432260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4432260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4432260 prefixEnd_4432260 := by exact prefixLift 4432260
  have htrace : WordTrace (prefixWord ++ tailWord_4432260) baseStart_4432260 baseEnd_4432260 := by
    simpa [prefixWord, tailWord_4432260, baseEnd_4432260] using wordTrace_append hprefix tailTrace_4432260
  have hstable : (prefixWord ++ tailWord_4432260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4432260).length < 2 ^ (prefixWord ++ tailWord_4432260).sum := by decide
  have hdescent : baseEnd_4432260 < baseStart_4432260 := by decide
  rcases family_descends (prefixWord ++ tailWord_4432260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4432337 : List Nat := [1, 2, 2, 1, 2, 1, 1, 7, 1, 5]
def baseStart_4432337 : Nat := 118140960795 + 4432337 * 2 ^ 59
def prefixEnd_4432337 : Nat := 4983230072969 + 3 ^ 40 * 4432337 * 2
def baseEnd_4432337 : Nat := 758639767902443398267853

theorem tailTrace_4432337 : CollatzResearch.WordTrace tailWord_4432337 prefixEnd_4432337 758639767902443398267853 := by
  unfold tailWord_4432337
  simp only [CollatzResearch.WordTrace]
  refine ⟨161660611343407506738223265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107773740895605004492148843 161660611343407506738223265)
  ·
    refine ⟨121245458507555630053667449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161660611343407506738223265 121245458507555630053667449)
    ·
      refine ⟨90934093880666722540250587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121245458507555630053667449 90934093880666722540250587)
      ·
        refine ⟨136401140821000083810375881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90934093880666722540250587 136401140821000083810375881)
        ·
          refine ⟨102300855615750062857781911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136401140821000083810375881 102300855615750062857781911)
          ·
            refine ⟨153451283423625094286672867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102300855615750062857781911 153451283423625094286672867)
            ·
              refine ⟨230176925135437641430009301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153451283423625094286672867 230176925135437641430009301)
              ·
                refine ⟨5394771682861819721015843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 230176925135437641430009301 5394771682861819721015843)
                ·
                  refine ⟨8092157524292729581523765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5394771682861819721015843 8092157524292729581523765)
                  ·
                    refine ⟨758639767902443398267853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8092157524292729581523765 758639767902443398267853)
                    ·
                      rfl

theorem cell23_4432337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 7, 1, 5].length) (baseStart_4432337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4432337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4432337 prefixEnd_4432337 := by exact prefixLift 4432337
  have htrace : WordTrace (prefixWord ++ tailWord_4432337) baseStart_4432337 baseEnd_4432337 := by
    simpa [prefixWord, tailWord_4432337, baseEnd_4432337] using wordTrace_append hprefix tailTrace_4432337
  have hstable : (prefixWord ++ tailWord_4432337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4432337).length < 2 ^ (prefixWord ++ tailWord_4432337).sum := by decide
  have hdescent : baseEnd_4432337 < baseStart_4432337 := by decide
  rcases family_descends (prefixWord ++ tailWord_4432337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4432367 : List Nat := [1, 1, 2, 1, 4, 1, 1, 2, 6, 4]
def baseStart_4432367 : Nat := 118140960795 + 4432367 * 2 ^ 59
def prefixEnd_4432367 : Nat := 4983230072969 + 3 ^ 40 * 4432367 * 2
def baseEnd_4432367 : Nat := 758644902708988359142807

theorem tailTrace_4432367 : CollatzResearch.WordTrace tailWord_4432367 prefixEnd_4432367 758644902708988359142807 := by
  unfold tailWord_4432367
  simp only [CollatzResearch.WordTrace]
  refine ⟨161661705533298821861815355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107774470355532547907876903 161661705533298821861815355)
  ·
    refine ⟨242492558299948232792723033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161661705533298821861815355 242492558299948232792723033)
    ·
      refine ⟨181869418724961174594542275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 242492558299948232792723033 181869418724961174594542275)
      ·
        refine ⟨272804128087441761891813413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181869418724961174594542275 272804128087441761891813413)
        ·
          refine ⟨51150774016395330354715015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 272804128087441761891813413 51150774016395330354715015)
          ·
            refine ⟨76726161024592995532072523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51150774016395330354715015 76726161024592995532072523)
            ·
              refine ⟨115089241536889493298108785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76726161024592995532072523 115089241536889493298108785)
              ·
                refine ⟨86316931152667119973581589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115089241536889493298108785 86316931152667119973581589)
                ·
                  refine ⟨4046106147781271248761637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 86316931152667119973581589 4046106147781271248761637)
                  ·
                    refine ⟨758644902708988359142807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4046106147781271248761637 758644902708988359142807)
                    ·
                      rfl

theorem cell23_4432367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 6, 4].length) (baseStart_4432367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4432367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4432367 prefixEnd_4432367 := by exact prefixLift 4432367
  have htrace : WordTrace (prefixWord ++ tailWord_4432367) baseStart_4432367 baseEnd_4432367 := by
    simpa [prefixWord, tailWord_4432367, baseEnd_4432367] using wordTrace_append hprefix tailTrace_4432367
  have hstable : (prefixWord ++ tailWord_4432367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4432367).length < 2 ^ (prefixWord ++ tailWord_4432367).sum := by decide
  have hdescent : baseEnd_4432367 < baseStart_4432367 := by decide
  rcases family_descends (prefixWord ++ tailWord_4432367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4432374 : List Nat := [5, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4]
def baseStart_4432374 : Nat := 118140960795 + 4432374 * 2 ^ 59
def prefixEnd_4432374 : Nat := 4983230072969 + 3 ^ 40 * 4432374 * 2
def baseEnd_4432374 : Nat := 2275938302491546550040889

theorem tailTrace_4432374 : CollatzResearch.WordTrace tailWord_4432374 prefixEnd_4432374 2275938302491546550040889 := by
  unfold tailWord_4432374
  simp only [CollatzResearch.WordTrace]
  refine ⟨10103872552767091378582511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 107774640562848974704880117 10103872552767091378582511)
  ·
    refine ⟨15155808829150637067873767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10103872552767091378582511 15155808829150637067873767)
    ·
      refine ⟨22733713243725955601810651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15155808829150637067873767 22733713243725955601810651)
      ·
        refine ⟨34100569865588933402715977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22733713243725955601810651 34100569865588933402715977)
        ·
          refine ⟨25575427399191700052036983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34100569865588933402715977 25575427399191700052036983)
          ·
            refine ⟨38363141098787550078055475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25575427399191700052036983 38363141098787550078055475)
            ·
              refine ⟨57544711648181325117083213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38363141098787550078055475 57544711648181325117083213)
              ·
                refine ⟨21579266868067996918906205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57544711648181325117083213 21579266868067996918906205)
                ·
                  refine ⟨8092225075525498844589827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21579266868067996918906205 8092225075525498844589827)
                  ·
                    refine ⟨12138337613288248266884741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8092225075525498844589827 12138337613288248266884741)
                    ·
                      refine ⟨2275938302491546550040889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12138337613288248266884741 2275938302491546550040889)
                      ·
                        rfl

theorem cell23_4432374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_4432374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4432374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4432374 prefixEnd_4432374 := by exact prefixLift 4432374
  have htrace : WordTrace (prefixWord ++ tailWord_4432374) baseStart_4432374 baseEnd_4432374 := by
    simpa [prefixWord, tailWord_4432374, baseEnd_4432374] using wordTrace_append hprefix tailTrace_4432374
  have hstable : (prefixWord ++ tailWord_4432374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4432374).length < 2 ^ (prefixWord ++ tailWord_4432374).sum := by decide
  have hdescent : baseEnd_4432374 < baseStart_4432374 := by decide
  rcases family_descends (prefixWord ++ tailWord_4432374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4432387 : List Nat := [1, 1, 1, 3, 2, 1, 3, 4, 1, 2, 4]
def baseStart_4432387 : Nat := 118140960795 + 4432387 * 2 ^ 59
def prefixEnd_4432387 : Nat := 4983230072969 + 3 ^ 40 * 4432387 * 2
def baseEnd_4432387 : Nat := 2275944977740054999178329

theorem tailTrace_4432387 : CollatzResearch.WordTrace tailWord_4432387 prefixEnd_4432387 2275944977740054999178329 := by
  unfold tailWord_4432387
  simp only [CollatzResearch.WordTrace]
  refine ⟨161662434993226365277543415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107774956662150910185028943 161662434993226365277543415)
  ·
    refine ⟨242493652489839547916315123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161662434993226365277543415 242493652489839547916315123)
    ·
      refine ⟨363740478734759321874472685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242493652489839547916315123 363740478734759321874472685)
      ·
        refine ⟨136402679525534745702927257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 363740478734759321874472685 136402679525534745702927257)
        ·
          refine ⟨102302009644151059277195443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136402679525534745702927257 102302009644151059277195443)
          ·
            refine ⟨153453014466226588915793165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102302009644151059277195443 153453014466226588915793165)
            ·
              refine ⟨57544880424834970843422437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 153453014466226588915793165 57544880424834970843422437)
              ·
                refine ⟨10789665079656557033141707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57544880424834970843422437 10789665079656557033141707)
                ·
                  refine ⟨16184497619484835549712561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10789665079656557033141707 16184497619484835549712561)
                  ·
                    refine ⟨12138373214613626662284421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16184497619484835549712561 12138373214613626662284421)
                    ·
                      refine ⟨2275944977740054999178329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12138373214613626662284421 2275944977740054999178329)
                      ·
                        rfl

theorem cell23_4432387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4, 1, 2, 4].length) (baseStart_4432387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4432387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4432387 prefixEnd_4432387 := by exact prefixLift 4432387
  have htrace : WordTrace (prefixWord ++ tailWord_4432387) baseStart_4432387 baseEnd_4432387 := by
    simpa [prefixWord, tailWord_4432387, baseEnd_4432387] using wordTrace_append hprefix tailTrace_4432387
  have hstable : (prefixWord ++ tailWord_4432387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4432387).length < 2 ^ (prefixWord ++ tailWord_4432387).sum := by decide
  have hdescent : baseEnd_4432387 < baseStart_4432387 := by decide
  rcases family_descends (prefixWord ++ tailWord_4432387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4432388 : List Nat := [2, 3, 2, 3, 1, 3, 2, 1, 1, 5]
def baseStart_4432388 : Nat := 118140960795 + 4432388 * 2 ^ 59
def prefixEnd_4432388 : Nat := 4983230072969 + 3 ^ 40 * 4432388 * 2
def baseEnd_4432388 : Nat := 758648497073569831755275

theorem tailTrace_4432388 : CollatzResearch.WordTrace tailWord_4432388 prefixEnd_4432388 758648497073569831755275 := by
  unfold tailWord_4432388
  simp only [CollatzResearch.WordTrace]
  refine ⟨80831235733111371224164909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107774980977481828298886545 80831235733111371224164909)
  ·
    refine ⟨30311713399916764209061841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80831235733111371224164909 30311713399916764209061841)
    ·
      refine ⟨22733785049937573156796381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30311713399916764209061841 22733785049937573156796381)
      ·
        refine ⟨8525169393726589933798643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22733785049937573156796381 8525169393726589933798643)
        ·
          refine ⟨12787754090589884900697965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8525169393726589933798643 12787754090589884900697965)
          ·
            refine ⟨4795407783971206837761737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12787754090589884900697965 4795407783971206837761737)
            ·
              refine ⟨3596555837978405128321303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4795407783971206837761737 3596555837978405128321303)
              ·
                refine ⟨5394833756967607692481955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3596555837978405128321303 5394833756967607692481955)
                ·
                  refine ⟨8092250635451411538722933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5394833756967607692481955 8092250635451411538722933)
                  ·
                    refine ⟨758648497073569831755275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8092250635451411538722933 758648497073569831755275)
                    ·
                      rfl

theorem cell23_4432388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2, 1, 1, 5].length) (baseStart_4432388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4432388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4432388 prefixEnd_4432388 := by exact prefixLift 4432388
  have htrace : WordTrace (prefixWord ++ tailWord_4432388) baseStart_4432388 baseEnd_4432388 := by
    simpa [prefixWord, tailWord_4432388, baseEnd_4432388] using wordTrace_append hprefix tailTrace_4432388
  have hstable : (prefixWord ++ tailWord_4432388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4432388).length < 2 ^ (prefixWord ++ tailWord_4432388).sum := by decide
  have hdescent : baseEnd_4432388 < baseStart_4432388 := by decide
  rcases family_descends (prefixWord ++ tailWord_4432388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4432391 : List Nat := [1, 1, 4, 3, 3, 1, 1, 3, 1, 1, 4]
def baseStart_4432391 : Nat := 118140960795 + 4432391 * 2 ^ 59
def prefixEnd_4432391 : Nat := 4983230072969 + 3 ^ 40 * 4432391 * 2
def baseEnd_4432391 : Nat := 2275947031662672983528311

theorem tailTrace_4432391 : CollatzResearch.WordTrace tailWord_4432391 prefixEnd_4432391 2275947031662672983528311 := by
  unfold tailWord_4432391
  simp only [CollatzResearch.WordTrace]
  refine ⟨161662580885211873960689027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107775053923474582640459351 161662580885211873960689027)
  ·
    refine ⟨242493871327817810941033541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161662580885211873960689027 242493871327817810941033541)
    ·
      refine ⟨45467600873965839551443789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 242493871327817810941033541 45467600873965839551443789)
      ·
        refine ⟨17050350327737189831791421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45467600873965839551443789 17050350327737189831791421)
        ·
          refine ⟨6393881372901446186921783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17050350327737189831791421 6393881372901446186921783)
          ·
            refine ⟨9590822059352169280382675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6393881372901446186921783 9590822059352169280382675)
            ·
              refine ⟨14386233089028253920574013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9590822059352169280382675 14386233089028253920574013)
              ·
                refine ⟨5394837408385595220215255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14386233089028253920574013 5394837408385595220215255)
                ·
                  refine ⟨8092256112578392830322883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5394837408385595220215255 8092256112578392830322883)
                  ·
                    refine ⟨12138384168867589245484325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8092256112578392830322883 12138384168867589245484325)
                    ·
                      refine ⟨2275947031662672983528311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12138384168867589245484325 2275947031662672983528311)
                      ·
                        rfl

theorem cell23_4432391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_4432391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4432391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4432391 prefixEnd_4432391 := by exact prefixLift 4432391
  have htrace : WordTrace (prefixWord ++ tailWord_4432391) baseStart_4432391 baseEnd_4432391 := by
    simpa [prefixWord, tailWord_4432391, baseEnd_4432391] using wordTrace_append hprefix tailTrace_4432391
  have hstable : (prefixWord ++ tailWord_4432391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4432391).length < 2 ^ (prefixWord ++ tailWord_4432391).sum := by decide
  have hdescent : baseEnd_4432391 < baseStart_4432391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4432391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4432408 : List Nat := [2, 1, 2, 3, 3, 2, 2, 1, 3, 2, 2]
def baseStart_4432408 : Nat := 118140960795 + 4432408 * 2 ^ 59
def prefixEnd_4432408 : Nat := 4983230072969 + 3 ^ 40 * 4432408 * 2
def baseEnd_4432408 : Nat := 2275955760833799417015733

theorem tailTrace_4432408 : CollatzResearch.WordTrace tailWord_4432408 prefixEnd_4432408 2275955760833799417015733 := by
  unfold tailWord_4432408
  simp only [CollatzResearch.WordTrace]
  refine ⟨80831600463075142932028939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107775467284100190576038585 80831600463075142932028939)
  ·
    refine ⟨121247400694612714398043409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80831600463075142932028939 121247400694612714398043409)
    ·
      refine ⟨90935550520959535798532557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121247400694612714398043409 90935550520959535798532557)
      ·
        refine ⟨34100831445359825924449709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90935550520959535798532557 34100831445359825924449709)
        ·
          refine ⟨12787811792009934721668641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34100831445359825924449709 12787811792009934721668641)
          ·
            refine ⟨9590858844007451041251481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12787811792009934721668641 9590858844007451041251481)
            ·
              refine ⟨7193144133005588280938611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9590858844007451041251481 7193144133005588280938611)
              ·
                refine ⟨10789716199508382421407917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7193144133005588280938611 10789716199508382421407917)
                ·
                  refine ⟨4046143574815643408027969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10789716199508382421407917 4046143574815643408027969)
                  ·
                    refine ⟨3034607681111732556020977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4046143574815643408027969 3034607681111732556020977)
                    ·
                      refine ⟨2275955760833799417015733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3034607681111732556020977 2275955760833799417015733)
                      ·
                        rfl

theorem cell23_4432408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 1, 3, 2, 2].length) (baseStart_4432408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4432408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4432408 prefixEnd_4432408 := by exact prefixLift 4432408
  have htrace : WordTrace (prefixWord ++ tailWord_4432408) baseStart_4432408 baseEnd_4432408 := by
    simpa [prefixWord, tailWord_4432408, baseEnd_4432408] using wordTrace_append hprefix tailTrace_4432408
  have hstable : (prefixWord ++ tailWord_4432408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4432408).length < 2 ^ (prefixWord ++ tailWord_4432408).sum := by decide
  have hdescent : baseEnd_4432408 < baseStart_4432408 := by decide
  rcases family_descends (prefixWord ++ tailWord_4432408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4432437 : List Nat := [1, 3, 3, 1, 1, 2, 1, 1, 1, 4, 5]
def baseStart_4432437 : Nat := 118140960795 + 4432437 * 2 ^ 59
def prefixEnd_4432437 : Nat := 4983230072969 + 3 ^ 40 * 4432437 * 2
def baseEnd_4432437 : Nat := 2275970651772779803553099

theorem tailTrace_4432437 : CollatzResearch.WordTrace tailWord_4432437 prefixEnd_4432437 2275970651772779803553099 := by
  unfold tailWord_4432437
  simp only [CollatzResearch.WordTrace]
  refine ⟨161664258643045223816863565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107776172428696815877909043 161664258643045223816863565)
  ·
    refine ⟨60624096991141958931323837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161664258643045223816863565 60624096991141958931323837)
    ·
      refine ⟨22734036371678234599246439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60624096991141958931323837 22734036371678234599246439)
      ·
        refine ⟨34101054557517351898869659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22734036371678234599246439 34101054557517351898869659)
        ·
          refine ⟨51151581836276027848304489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34101054557517351898869659 51151581836276027848304489)
          ·
            refine ⟨38363686377207020886228367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51151581836276027848304489 38363686377207020886228367)
            ·
              refine ⟨57545529565810531329342551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38363686377207020886228367 57545529565810531329342551)
              ·
                refine ⟨86318294348715796994013827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57545529565810531329342551 86318294348715796994013827)
                ·
                  refine ⟨129477441523073695491020741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86318294348715796994013827 129477441523073695491020741)
                  ·
                    refine ⟨24277020285576317904566389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 129477441523073695491020741 24277020285576317904566389)
                    ·
                      refine ⟨2275970651772779803553099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24277020285576317904566389 2275970651772779803553099)
                      ·
                        rfl

theorem cell23_4432437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_4432437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4432437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4432437 prefixEnd_4432437 := by exact prefixLift 4432437
  have htrace : WordTrace (prefixWord ++ tailWord_4432437) baseStart_4432437 baseEnd_4432437 := by
    simpa [prefixWord, tailWord_4432437, baseEnd_4432437] using wordTrace_append hprefix tailTrace_4432437
  have hstable : (prefixWord ++ tailWord_4432437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4432437).length < 2 ^ (prefixWord ++ tailWord_4432437).sum := by decide
  have hdescent : baseEnd_4432437 < baseStart_4432437 := by decide
  rcases family_descends (prefixWord ++ tailWord_4432437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4432464 : List Nat := [2, 1, 1, 1, 1, 3, 2, 1, 5, 4, 2]
def baseStart_4432464 : Nat := 118140960795 + 4432464 * 2 ^ 59
def prefixEnd_4432464 : Nat := 4983230072969 + 3 ^ 40 * 4432464 * 2
def baseEnd_4432464 : Nat := 2275984515750451197915475

theorem tailTrace_4432464 : CollatzResearch.WordTrace tailWord_4432464 prefixEnd_4432464 2275984515750451197915475 := by
  unfold tailWord_4432464
  simp only [CollatzResearch.WordTrace]
  refine ⟨80832621706973703714048223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107776828942631604952064297 80832621706973703714048223)
  ·
    refine ⟨121248932560460555571072335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80832621706973703714048223 121248932560460555571072335)
    ·
      refine ⟨181873398840690833356608503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121248932560460555571072335 181873398840690833356608503)
      ·
        refine ⟨272810098261036250034912755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181873398840690833356608503 272810098261036250034912755)
        ·
          refine ⟨409215147391554375052369133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272810098261036250034912755 409215147391554375052369133)
          ·
            refine ⟨153455680271832890644638425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 409215147391554375052369133 153455680271832890644638425)
            ·
              refine ⟨115091760203874667983478819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 153455680271832890644638425 115091760203874667983478819)
              ·
                refine ⟨172637640305812001975218229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115091760203874667983478819 172637640305812001975218229)
                ·
                  refine ⟨16184778778669875185176709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 172637640305812001975218229 16184778778669875185176709)
                  ·
                    refine ⟨3034646021000601597220633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16184778778669875185176709 3034646021000601597220633)
                    ·
                      refine ⟨2275984515750451197915475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3034646021000601597220633 2275984515750451197915475)
                      ·
                        rfl

theorem cell23_4432464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 5, 4, 2].length) (baseStart_4432464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4432464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4432464 prefixEnd_4432464 := by exact prefixLift 4432464
  have htrace : WordTrace (prefixWord ++ tailWord_4432464) baseStart_4432464 baseEnd_4432464 := by
    simpa [prefixWord, tailWord_4432464, baseEnd_4432464] using wordTrace_append hprefix tailTrace_4432464
  have hstable : (prefixWord ++ tailWord_4432464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4432464).length < 2 ^ (prefixWord ++ tailWord_4432464).sum := by decide
  have hdescent : baseEnd_4432464 < baseStart_4432464 := by decide
  rcases family_descends (prefixWord ++ tailWord_4432464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4432485 : List Nat := [1, 3, 1, 3, 4, 2, 1, 2, 1, 3, 2]
def baseStart_4432485 : Nat := 118140960795 + 4432485 * 2 ^ 59
def prefixEnd_4432485 : Nat := 4983230072969 + 3 ^ 40 * 4432485 * 2
def baseEnd_4432485 : Nat := 2275995298844195615752879

theorem tailTrace_4432485 : CollatzResearch.WordTrace tailWord_4432485 prefixEnd_4432485 2275995298844195615752879 := by
  unfold tailWord_4432485
  simp only [CollatzResearch.WordTrace]
  refine ⟨161666009346871328014610909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107777339564580885343073939 161666009346871328014610909)
  ·
    refine ⟨60624753505076748005479091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161666009346871328014610909 60624753505076748005479091)
    ·
      refine ⟨90937130257615122008218637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60624753505076748005479091 90937130257615122008218637)
      ·
        refine ⟨34101423846605670753081989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90937130257615122008218637 34101423846605670753081989)
        ·
          refine ⟨6394016971238563266202873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34101423846605670753081989 6394016971238563266202873)
          ·
            refine ⟨4795512728428922449652155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6394016971238563266202873 4795512728428922449652155)
            ·
              refine ⟨7193269092643383674478233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4795512728428922449652155 7193269092643383674478233)
              ·
                refine ⟨5394951819482537755858675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7193269092643383674478233 5394951819482537755858675)
                ·
                  refine ⟨8092427729223806633788013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5394951819482537755858675 8092427729223806633788013)
                  ·
                    refine ⟨3034660398458927487670505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8092427729223806633788013 3034660398458927487670505)
                    ·
                      refine ⟨2275995298844195615752879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3034660398458927487670505 2275995298844195615752879)
                      ·
                        rfl

theorem cell23_4432485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 2, 1, 3, 2].length) (baseStart_4432485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4432485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4432485 prefixEnd_4432485 := by exact prefixLift 4432485
  have htrace : WordTrace (prefixWord ++ tailWord_4432485) baseStart_4432485 baseEnd_4432485 := by
    simpa [prefixWord, tailWord_4432485, baseEnd_4432485] using wordTrace_append hprefix tailTrace_4432485
  have hstable : (prefixWord ++ tailWord_4432485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4432485).length < 2 ^ (prefixWord ++ tailWord_4432485).sum := by decide
  have hdescent : baseEnd_4432485 < baseStart_4432485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4432485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4432487 : List Nat := [1, 1, 5, 1, 1, 1, 1, 3, 9]
def baseStart_4432487 : Nat := 118140960795 + 4432487 * 2 ^ 59
def prefixEnd_4432487 : Nat := 4983230072969 + 3 ^ 40 * 4432487 * 2
def baseEnd_4432487 : Nat := 252888480645056067547541

theorem tailTrace_4432487 : CollatzResearch.WordTrace tailWord_4432487 prefixEnd_4432487 252888480645056067547541 := by
  unfold tailWord_4432487
  simp only [CollatzResearch.WordTrace]
  refine ⟨161666082292864082356183715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107777388195242721570789143 161666082292864082356183715)
  ·
    refine ⟨242499123439296123534275573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161666082292864082356183715 242499123439296123534275573)
    ·
      refine ⟨22734292822434011581338335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 242499123439296123534275573 22734292822434011581338335)
      ·
        refine ⟨34101439233651017372007503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22734292822434011581338335 34101439233651017372007503)
        ·
          refine ⟨51152158850476526058011255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34101439233651017372007503 51152158850476526058011255)
          ·
            refine ⟨76728238275714789087016883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51152158850476526058011255 76728238275714789087016883)
            ·
              refine ⟨115092357413572183630525325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76728238275714789087016883 115092357413572183630525325)
              ·
                refine ⟨43159634030089568861446997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 115092357413572183630525325 43159634030089568861446997)
                ·
                  refine ⟨252888480645056067547541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 43159634030089568861446997 252888480645056067547541)
                  ·
                    rfl

theorem cell23_4432487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 9].length) (baseStart_4432487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4432487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4432487 prefixEnd_4432487 := by exact prefixLift 4432487
  have htrace : WordTrace (prefixWord ++ tailWord_4432487) baseStart_4432487 baseEnd_4432487 := by
    simpa [prefixWord, tailWord_4432487, baseEnd_4432487] using wordTrace_append hprefix tailTrace_4432487
  have hstable : (prefixWord ++ tailWord_4432487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4432487).length < 2 ^ (prefixWord ++ tailWord_4432487).sum := by decide
  have hdescent : baseEnd_4432487 < baseStart_4432487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4432487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4432498 : List Nat := [3, 2, 1, 2, 4, 1, 1, 2, 1, 4, 2]
def baseStart_4432498 : Nat := 118140960795 + 4432498 * 2 ^ 59
def prefixEnd_4432498 : Nat := 4983230072969 + 3 ^ 40 * 4432498 * 2
def baseEnd_4432498 : Nat := 2276001974092704064890319

theorem tailTrace_4432498 : CollatzResearch.WordTrace tailWord_4432498 prefixEnd_4432498 2276001974092704064890319 := by
  unfold tailWord_4432498
  simp only [CollatzResearch.WordTrace]
  refine ⟨40416620873956057808708537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107777655663882820823222765 40416620873956057808708537)
  ·
    refine ⟨30312465655467043356531403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40416620873956057808708537 30312465655467043356531403)
    ·
      refine ⟨45468698483200565034797105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30312465655467043356531403 45468698483200565034797105)
      ·
        refine ⟨34101523862400423776097829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45468698483200565034797105 34101523862400423776097829)
        ·
          refine ⟨6394035724200079458018343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34101523862400423776097829 6394035724200079458018343)
          ·
            refine ⟨9591053586300119187027515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6394035724200079458018343 9591053586300119187027515)
            ·
              refine ⟨14386580379450178780541273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9591053586300119187027515 14386580379450178780541273)
              ·
                refine ⟨10789935284587634085405955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14386580379450178780541273 10789935284587634085405955)
                ·
                  refine ⟨16184902926881451128108933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10789935284587634085405955 16184902926881451128108933)
                  ·
                    refine ⟨3034669298790272086520425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16184902926881451128108933 3034669298790272086520425)
                    ·
                      refine ⟨2276001974092704064890319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3034669298790272086520425 2276001974092704064890319)
                      ·
                        rfl

theorem cell23_4432498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 2, 1, 4, 2].length) (baseStart_4432498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4432498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4432498 prefixEnd_4432498 := by exact prefixLift 4432498
  have htrace : WordTrace (prefixWord ++ tailWord_4432498) baseStart_4432498 baseEnd_4432498 := by
    simpa [prefixWord, tailWord_4432498, baseEnd_4432498] using wordTrace_append hprefix tailTrace_4432498
  have hstable : (prefixWord ++ tailWord_4432498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4432498).length < 2 ^ (prefixWord ++ tailWord_4432498).sum := by decide
  have hdescent : baseEnd_4432498 < baseStart_4432498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4432498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4432502 : List Nat := [5, 1, 1, 2, 3, 1, 3, 1, 1, 3, 2]
def baseStart_4432502 : Nat := 118140960795 + 4432502 * 2 ^ 59
def prefixEnd_4432502 : Nat := 4983230072969 + 3 ^ 40 * 4432502 * 2
def baseEnd_4432502 : Nat := 2276004028015322049240301

theorem tailTrace_4432502 : CollatzResearch.WordTrace tailWord_4432502 prefixEnd_4432502 2276004028015322049240301 := by
  unfold tailWord_4432502
  simp only [CollatzResearch.WordTrace]
  refine ⟨10104164336738108744873735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 107777752925206493278653173 10104164336738108744873735)
  ·
    refine ⟨15156246505107163117310603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10104164336738108744873735 15156246505107163117310603)
    ·
      refine ⟨22734369757660744675965905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15156246505107163117310603 22734369757660744675965905)
      ·
        refine ⟨17050777318245558506974429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22734369757660744675965905 17050777318245558506974429)
        ·
          refine ⟨6394041494342084440115411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17050777318245558506974429 6394041494342084440115411)
          ·
            refine ⟨9591062241513126660173117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6394041494342084440115411 9591062241513126660173117)
            ·
              refine ⟨3596648340567422497564919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9591062241513126660173117 3596648340567422497564919)
              ·
                refine ⟨5394972510851133746347379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3596648340567422497564919 5394972510851133746347379)
                ·
                  refine ⟨8092458766276700619521069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5394972510851133746347379 8092458766276700619521069)
                  ·
                    refine ⟨3034672037353762732320401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8092458766276700619521069 3034672037353762732320401)
                    ·
                      refine ⟨2276004028015322049240301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3034672037353762732320401 2276004028015322049240301)
                      ·
                        rfl

theorem cell23_4432502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_4432502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4432502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4432502 prefixEnd_4432502 := by exact prefixLift 4432502
  have htrace : WordTrace (prefixWord ++ tailWord_4432502) baseStart_4432502 baseEnd_4432502 := by
    simpa [prefixWord, tailWord_4432502, baseEnd_4432502] using wordTrace_append hprefix tailTrace_4432502
  have hstable : (prefixWord ++ tailWord_4432502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4432502).length < 2 ^ (prefixWord ++ tailWord_4432502).sum := by decide
  have hdescent : baseEnd_4432502 < baseStart_4432502 := by decide
  rcases family_descends (prefixWord ++ tailWord_4432502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4432547 : List Nat := [1, 1, 1, 4, 1, 1, 2, 1, 1, 10]
def baseStart_4432547 : Nat := 118140960795 + 4432547 * 2 ^ 59
def prefixEnd_4432547 : Nat := 4983230072969 + 3 ^ 40 * 4432547 * 2
def baseEnd_4432547 : Nat := 758675711548258124392531

theorem tailTrace_4432547 : CollatzResearch.WordTrace tailWord_4432547 prefixEnd_4432547 758675711548258124392531 := by
  unfold tailWord_4432547
  simp only [CollatzResearch.WordTrace]
  refine ⟨161668270672646712603367895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107778847115097808402245263 161668270672646712603367895)
  ·
    refine ⟨242502406008970068905051843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161668270672646712603367895 242502406008970068905051843)
    ·
      refine ⟨363753609013455103357577765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242502406008970068905051843 363753609013455103357577765)
      ·
        refine ⟨68203801690022831879545831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 363753609013455103357577765 68203801690022831879545831)
        ·
          refine ⟨102305702535034247819318747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68203801690022831879545831 102305702535034247819318747)
          ·
            refine ⟨153458553802551371728978121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102305702535034247819318747 153458553802551371728978121)
            ·
              refine ⟨115093915351913528796733591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 153458553802551371728978121 115093915351913528796733591)
              ·
                refine ⟨172640873027870293195100387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115093915351913528796733591 172640873027870293195100387)
                ·
                  refine ⟨258961309541805439792650581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 172640873027870293195100387 258961309541805439792650581)
                  ·
                    refine ⟨758675711548258124392531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 258961309541805439792650581 758675711548258124392531)
                    ·
                      rfl

theorem cell23_4432547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 10].length) (baseStart_4432547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4432547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4432547 prefixEnd_4432547 := by exact prefixLift 4432547
  have htrace : WordTrace (prefixWord ++ tailWord_4432547) baseStart_4432547 baseEnd_4432547 := by
    simpa [prefixWord, tailWord_4432547, baseEnd_4432547] using wordTrace_append hprefix tailTrace_4432547
  have hstable : (prefixWord ++ tailWord_4432547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4432547).length < 2 ^ (prefixWord ++ tailWord_4432547).sum := by decide
  have hdescent : baseEnd_4432547 < baseStart_4432547 := by decide
  rcases family_descends (prefixWord ++ tailWord_4432547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4432566 : List Nat := [5, 1, 3, 1, 3, 1, 1, 2, 2, 2, 2]
def baseStart_4432566 : Nat := 118140960795 + 4432566 * 2 ^ 59
def prefixEnd_4432566 : Nat := 4983230072969 + 3 ^ 40 * 4432566 * 2
def baseEnd_4432566 : Nat := 2276036890777209798840007

theorem tailTrace_4432566 : CollatzResearch.WordTrace tailWord_4432566 prefixEnd_4432566 2276036890777209798840007 := by
  unfold tailWord_4432566
  simp only [CollatzResearch.WordTrace]
  refine ⟨10104310228723617428019347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 107779309106385252565539701 10104310228723617428019347)
  ·
    refine ⟨15156465343085426142029021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10104310228723617428019347 15156465343085426142029021)
    ·
      refine ⟨5683674503657034803260883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15156465343085426142029021 5683674503657034803260883)
      ·
        refine ⟨8525511755485552204891325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5683674503657034803260883 8525511755485552204891325)
        ·
          refine ⟨3197066908307082076834247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8525511755485552204891325 3197066908307082076834247)
          ·
            refine ⟨4795600362460623115251371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3197066908307082076834247 4795600362460623115251371)
            ·
              refine ⟨7193400543690934672877057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4795600362460623115251371 7193400543690934672877057)
              ·
                refine ⟨5395050407768201004657793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7193400543690934672877057 5395050407768201004657793)
                ·
                  refine ⟨4046287805826150753493345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5395050407768201004657793 4046287805826150753493345)
                  ·
                    refine ⟨3034715854369613065120009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4046287805826150753493345 3034715854369613065120009)
                    ·
                      refine ⟨2276036890777209798840007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3034715854369613065120009 2276036890777209798840007)
                      ·
                        rfl

theorem cell23_4432566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_4432566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4432566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4432566 prefixEnd_4432566 := by exact prefixLift 4432566
  have htrace : WordTrace (prefixWord ++ tailWord_4432566) baseStart_4432566 baseEnd_4432566 := by
    simpa [prefixWord, tailWord_4432566, baseEnd_4432566] using wordTrace_append hprefix tailTrace_4432566
  have hstable : (prefixWord ++ tailWord_4432566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4432566).length < 2 ^ (prefixWord ++ tailWord_4432566).sum := by decide
  have hdescent : baseEnd_4432566 < baseStart_4432566 := by decide
  rcases family_descends (prefixWord ++ tailWord_4432566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4432588 : List Nat := [2, 2, 1, 5, 1, 1, 2, 1, 2, 4, 2]
def baseStart_4432588 : Nat := 118140960795 + 4432588 * 2 ^ 59
def prefixEnd_4432588 : Nat := 4983230072969 + 3 ^ 40 * 4432588 * 2
def baseEnd_4432588 : Nat := 2276048187351608712764905

theorem tailTrace_4432588 : CollatzResearch.WordTrace tailWord_4432588 prefixEnd_4432588 2276048187351608712764905 := by
  unfold tailWord_4432588
  simp only [CollatzResearch.WordTrace]
  refine ⟨80834883032749088302805209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107779844043665451070406945 80834883032749088302805209)
  ·
    refine ⟨60626162274561816227103907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80834883032749088302805209 60626162274561816227103907)
    ·
      refine ⟨90939243411842724340655861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60626162274561816227103907 90939243411842724340655861)
      ·
        refine ⟨8525554069860255406936487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 90939243411842724340655861 8525554069860255406936487)
        ·
          refine ⟨12788331104790383110404731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8525554069860255406936487 12788331104790383110404731)
          ·
            refine ⟨19182496657185574665607097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12788331104790383110404731 19182496657185574665607097)
            ·
              refine ⟨14386872492889180999205323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19182496657185574665607097 14386872492889180999205323)
              ·
                refine ⟨21580308739333771498807985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14386872492889180999205323 21580308739333771498807985)
                ·
                  refine ⟨16185231554500328624105989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21580308739333771498807985 16185231554500328624105989)
                  ·
                    refine ⟨3034730916468811617019873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16185231554500328624105989 3034730916468811617019873)
                    ·
                      refine ⟨2276048187351608712764905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3034730916468811617019873 2276048187351608712764905)
                      ·
                        rfl

theorem cell23_4432588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_4432588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4432588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4432588 prefixEnd_4432588 := by exact prefixLift 4432588
  have htrace : WordTrace (prefixWord ++ tailWord_4432588) baseStart_4432588 baseEnd_4432588 := by
    simpa [prefixWord, tailWord_4432588, baseEnd_4432588] using wordTrace_append hprefix tailTrace_4432588
  have hstable : (prefixWord ++ tailWord_4432588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4432588).length < 2 ^ (prefixWord ++ tailWord_4432588).sum := by decide
  have hdescent : baseEnd_4432588 < baseStart_4432588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4432588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4432661 : List Nat := [1, 3, 2, 1, 2, 2, 3, 1, 3, 1, 4]
def baseStart_4432661 : Nat := 118140960795 + 4432661 * 2 ^ 59
def prefixEnd_4432661 : Nat := 4983230072969 + 3 ^ 40 * 4432661 * 2
def baseEnd_4432661 : Nat := 2276085671439386927152069

theorem tailTrace_4432661 : CollatzResearch.WordTrace tailWord_4432661 prefixEnd_4432661 2276085671439386927152069 := by
  unfold tailWord_4432661
  simp only [CollatzResearch.WordTrace]
  refine ⟨161672428594233710073017837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107781619062822473382011891 161672428594233710073017837)
  ·
    refine ⟨60627160722837641277381689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161672428594233710073017837 60627160722837641277381689)
    ·
      refine ⟨45470370542128230958036267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60627160722837641277381689 45470370542128230958036267)
      ·
        refine ⟨68205555813192346437054401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45470370542128230958036267 68205555813192346437054401)
        ·
          refine ⟨51154166859894259827790801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68205555813192346437054401 51154166859894259827790801)
          ·
            refine ⟨38365625144920694870843101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51154166859894259827790801 38365625144920694870843101)
            ·
              refine ⟨14387109429345260576566163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38365625144920694870843101 14387109429345260576566163)
              ·
                refine ⟨21580664144017890864849245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14387109429345260576566163 21580664144017890864849245)
                ·
                  refine ⟨8092749054006709074318467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21580664144017890864849245 8092749054006709074318467)
                  ·
                    refine ⟨12139123581010063611477701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8092749054006709074318467 12139123581010063611477701)
                    ·
                      refine ⟨2276085671439386927152069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12139123581010063611477701 2276085671439386927152069)
                      ·
                        rfl

theorem cell23_4432661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 3, 1, 4].length) (baseStart_4432661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4432661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4432661 prefixEnd_4432661 := by exact prefixLift 4432661
  have htrace : WordTrace (prefixWord ++ tailWord_4432661) baseStart_4432661 baseEnd_4432661 := by
    simpa [prefixWord, tailWord_4432661, baseEnd_4432661] using wordTrace_append hprefix tailTrace_4432661
  have hstable : (prefixWord ++ tailWord_4432661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4432661).length < 2 ^ (prefixWord ++ tailWord_4432661).sum := by decide
  have hdescent : baseEnd_4432661 < baseStart_4432661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4432661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4432671 : List Nat := [1, 1, 2, 4, 2, 3, 1, 2, 1, 6]
def baseStart_4432671 : Nat := 118140960795 + 4432671 * 2 ^ 59
def prefixEnd_4432671 : Nat := 4983230072969 + 3 ^ 40 * 4432671 * 2
def baseEnd_4432671 : Nat := 758696935415310629342341

theorem tailTrace_4432671 : CollatzResearch.WordTrace tailWord_4432671 prefixEnd_4432671 758696935415310629342341 := by
  unfold tailWord_4432671
  simp only [CollatzResearch.WordTrace]
  refine ⟨161672793324197481780881867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107781862216131654520587911 161672793324197481780881867)
  ·
    refine ⟨242509189986296222671322801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161672793324197481780881867 242509189986296222671322801)
    ·
      refine ⟨181881892489722167003492101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 242509189986296222671322801 181881892489722167003492101)
      ·
        refine ⟨34102854841822906313154769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 181881892489722167003492101 34102854841822906313154769)
        ·
          refine ⟨25577141131367179734866077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34102854841822906313154769 25577141131367179734866077)
          ·
            refine ⟨9591427924262692400574779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25577141131367179734866077 9591427924262692400574779)
            ·
              refine ⟨14387141886394038600862169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9591427924262692400574779 14387141886394038600862169)
              ·
                refine ⟨10790356414795528950646627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14387141886394038600862169 10790356414795528950646627)
                ·
                  refine ⟨16185534622193293425969941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10790356414795528950646627 16185534622193293425969941)
                  ·
                    refine ⟨758696935415310629342341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16185534622193293425969941 758696935415310629342341)
                    ·
                      rfl

theorem cell23_4432671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 2, 1, 6].length) (baseStart_4432671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4432671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4432671 prefixEnd_4432671 := by exact prefixLift 4432671
  have htrace : WordTrace (prefixWord ++ tailWord_4432671) baseStart_4432671 baseEnd_4432671 := by
    simpa [prefixWord, tailWord_4432671, baseEnd_4432671] using wordTrace_append hprefix tailTrace_4432671
  have hstable : (prefixWord ++ tailWord_4432671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4432671).length < 2 ^ (prefixWord ++ tailWord_4432671).sum := by decide
  have hdescent : baseEnd_4432671 < baseStart_4432671 := by decide
  rcases family_descends (prefixWord ++ tailWord_4432671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4432704 : List Nat := [2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 6]
def baseStart_4432704 : Nat := 118140960795 + 4432704 * 2 ^ 59
def prefixEnd_4432704 : Nat := 4983230072969 + 3 ^ 40 * 4432704 * 2
def baseEnd_4432704 : Nat := 2276107751107530258914371

theorem tailTrace_4432704 : CollatzResearch.WordTrace tailWord_4432704 prefixEnd_4432704 2276107751107530258914371 := by
  unfold tailWord_4432704
  simp only [CollatzResearch.WordTrace]
  refine ⟨80836998466538964208416583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107782664622051952277888777 80836998466538964208416583)
  ·
    refine ⟨121255497699808446312624875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80836998466538964208416583 121255497699808446312624875)
    ·
      refine ⟨181883246549712669468937313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121255497699808446312624875 181883246549712669468937313)
      ·
        refine ⟨136412434912284502101702985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181883246549712669468937313 136412434912284502101702985)
        ·
          refine ⟨102309326184213376576277239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136412434912284502101702985 102309326184213376576277239)
          ·
            refine ⟨153463989276320064864415859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102309326184213376576277239 153463989276320064864415859)
            ·
              refine ⟨230195983914480097296623789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153463989276320064864415859 230195983914480097296623789)
              ·
                refine ⟨86323493967930036486233921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 230195983914480097296623789 86323493967930036486233921)
                ·
                  refine ⟨64742620475947527364675441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86323493967930036486233921 64742620475947527364675441)
                  ·
                    refine ⟨48556965356960645523506581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 64742620475947527364675441 48556965356960645523506581)
                    ·
                      refine ⟨2276107751107530258914371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48556965356960645523506581 2276107751107530258914371)
                      ·
                        rfl

theorem cell23_4432704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 6].length) (baseStart_4432704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4432704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4432704 prefixEnd_4432704 := by exact prefixLift 4432704
  have htrace : WordTrace (prefixWord ++ tailWord_4432704) baseStart_4432704 baseEnd_4432704 := by
    simpa [prefixWord, tailWord_4432704, baseEnd_4432704] using wordTrace_append hprefix tailTrace_4432704
  have hstable : (prefixWord ++ tailWord_4432704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4432704).length < 2 ^ (prefixWord ++ tailWord_4432704).sum := by decide
  have hdescent : baseEnd_4432704 < baseStart_4432704 := by decide
  rcases family_descends (prefixWord ++ tailWord_4432704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4432705 : List Nat := [1, 2, 5, 3, 1, 1, 2, 1, 1, 6]
def baseStart_4432705 : Nat := 118140960795 + 4432705 * 2 ^ 59
def prefixEnd_4432705 : Nat := 4983230072969 + 3 ^ 40 * 4432705 * 2
def baseEnd_4432705 : Nat := 758702754862728251667289

theorem tailTrace_4432705 : CollatzResearch.WordTrace tailWord_4432705 prefixEnd_4432705 758702754862728251667289 := by
  unfold tailWord_4432705
  simp only [CollatzResearch.WordTrace]
  refine ⟨161674033406074305587619569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107782688937382870391746379 161674033406074305587619569)
  ·
    refine ⟨121255525054555729190714677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161674033406074305587619569 121255525054555729190714677)
    ·
      refine ⟨11367705473864599611629501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 121255525054555729190714677 11367705473864599611629501)
      ·
        refine ⟨4262889552699224854361063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11367705473864599611629501 4262889552699224854361063)
        ·
          refine ⟨6394334329048837281541595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4262889552699224854361063 6394334329048837281541595)
          ·
            refine ⟨9591501493573255922312393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6394334329048837281541595 9591501493573255922312393)
            ·
              refine ⟨7193626120179941941734295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9591501493573255922312393 7193626120179941941734295)
              ·
                refine ⟨10790439180269912912601443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7193626120179941941734295 10790439180269912912601443)
                ·
                  refine ⟨16185658770404869368902165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10790439180269912912601443 16185658770404869368902165)
                  ·
                    refine ⟨758702754862728251667289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16185658770404869368902165 758702754862728251667289)
                    ·
                      rfl

theorem cell23_4432705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_4432705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4432705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4432705 prefixEnd_4432705 := by exact prefixLift 4432705
  have htrace : WordTrace (prefixWord ++ tailWord_4432705) baseStart_4432705 baseEnd_4432705 := by
    simpa [prefixWord, tailWord_4432705, baseEnd_4432705] using wordTrace_append hprefix tailTrace_4432705
  have hstable : (prefixWord ++ tailWord_4432705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4432705).length < 2 ^ (prefixWord ++ tailWord_4432705).sum := by decide
  have hdescent : baseEnd_4432705 < baseStart_4432705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4432705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4432732 : List Nat := [2, 2, 4, 2, 1, 1, 4, 1, 1, 2, 3]
def baseStart_4432732 : Nat := 118140960795 + 4432732 * 2 ^ 59
def prefixEnd_4432732 : Nat := 4983230072969 + 3 ^ 40 * 4432732 * 2
def baseEnd_4432732 : Nat := 2276122128565856149364243

theorem tailTrace_4432732 : CollatzResearch.WordTrace tailWord_4432732 prefixEnd_4432732 2276122128565856149364243 := by
  unfold tailWord_4432732
  simp only [CollatzResearch.WordTrace]
  refine ⟨80837509088488244599426225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107783345451317659465901633 80837509088488244599426225)
  ·
    refine ⟨60628131816366183449569669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80837509088488244599426225 60628131816366183449569669)
    ·
      refine ⟨11367774715568659396794313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60628131816366183449569669 11367774715568659396794313)
      ·
        refine ⟨8525831036676494547595735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11367774715568659396794313 8525831036676494547595735)
        ·
          refine ⟨12788746555014741821393603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8525831036676494547595735 12788746555014741821393603)
          ·
            refine ⟨19183119832522112732090405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12788746555014741821393603 19183119832522112732090405)
            ·
              refine ⟨3596834968597896137266951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19183119832522112732090405 3596834968597896137266951)
              ·
                refine ⟨5395252452896844205900427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3596834968597896137266951 5395252452896844205900427)
                ·
                  refine ⟨8092878679345266308850641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5395252452896844205900427 8092878679345266308850641)
                  ·
                    refine ⟨6069659009508949731637981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8092878679345266308850641 6069659009508949731637981)
                    ·
                      refine ⟨2276122128565856149364243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6069659009508949731637981 2276122128565856149364243)
                      ·
                        rfl

theorem cell23_4432732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_4432732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4432732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4432732 prefixEnd_4432732 := by exact prefixLift 4432732
  have htrace : WordTrace (prefixWord ++ tailWord_4432732) baseStart_4432732 baseEnd_4432732 := by
    simpa [prefixWord, tailWord_4432732, baseEnd_4432732] using wordTrace_append hprefix tailTrace_4432732
  have hstable : (prefixWord ++ tailWord_4432732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4432732).length < 2 ^ (prefixWord ++ tailWord_4432732).sum := by decide
  have hdescent : baseEnd_4432732 < baseStart_4432732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4432732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4432761 : List Nat := [1, 2, 1, 3, 2, 3, 2, 1, 2, 6]
def baseStart_4432761 : Nat := 118140960795 + 4432761 * 2 ^ 59
def prefixEnd_4432761 : Nat := 4983230072969 + 3 ^ 40 * 4432761 * 2
def baseEnd_4432761 : Nat := 758712339834945511967203

theorem tailTrace_4432761 : CollatzResearch.WordTrace tailWord_4432761 prefixEnd_4432761 758712339834945511967203 := by
  unfold tailWord_4432761
  simp only [CollatzResearch.WordTrace]
  refine ⟨161676075893871427151658137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107784050595914284767772091 161676075893871427151658137)
  ·
    refine ⟨121257056920403570363743603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161676075893871427151658137 121257056920403570363743603)
    ·
      refine ⟨181885585380605355545615405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121257056920403570363743603 181885585380605355545615405)
      ·
        refine ⟨68207094517727008329605777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 181885585380605355545615405 68207094517727008329605777)
        ·
          refine ⟨51155320888295256247204333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68207094517727008329605777 51155320888295256247204333)
          ·
            refine ⟨19183245333110721092701625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51155320888295256247204333 19183245333110721092701625)
            ·
              refine ⟨14387433999833040819526219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19183245333110721092701625 14387433999833040819526219)
              ·
                refine ⟨21581150999749561229289329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14387433999833040819526219 21581150999749561229289329)
                ·
                  refine ⟨16185863249812170921966997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21581150999749561229289329 16185863249812170921966997)
                  ·
                    refine ⟨758712339834945511967203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16185863249812170921966997 758712339834945511967203)
                    ·
                      rfl

theorem cell23_4432761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 2, 6].length) (baseStart_4432761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4432761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4432761 prefixEnd_4432761 := by exact prefixLift 4432761
  have htrace : WordTrace (prefixWord ++ tailWord_4432761) baseStart_4432761 baseEnd_4432761 := by
    simpa [prefixWord, tailWord_4432761, baseEnd_4432761] using wordTrace_append hprefix tailTrace_4432761
  have hstable : (prefixWord ++ tailWord_4432761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4432761).length < 2 ^ (prefixWord ++ tailWord_4432761).sum := by decide
  have hdescent : baseEnd_4432761 < baseStart_4432761 := by decide
  rcases family_descends (prefixWord ++ tailWord_4432761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4432768 : List Nat := [2, 1, 1, 2, 1, 2, 2, 5, 1, 4, 2]
def baseStart_4432768 : Nat := 118140960795 + 4432768 * 2 ^ 59
def prefixEnd_4432768 : Nat := 4983230072969 + 3 ^ 40 * 4432768 * 2
def baseEnd_4432768 : Nat := 2276140613869418008514077

theorem tailTrace_4432768 : CollatzResearch.WordTrace tailWord_4432768 prefixEnd_4432768 2276140613869418008514077 := by
  unfold tailWord_4432768
  simp only [CollatzResearch.WordTrace]
  refine ⟨80838165602423033673581479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107784220803230711564775305 80838165602423033673581479)
  ·
    refine ⟨121257248403634550510372219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80838165602423033673581479 121257248403634550510372219)
    ·
      refine ⟨181885872605451825765558329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121257248403634550510372219 181885872605451825765558329)
      ·
        refine ⟨136414404454088869324168747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181885872605451825765558329 136414404454088869324168747)
        ·
          refine ⟨204621606681133303986253121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136414404454088869324168747 204621606681133303986253121)
          ·
            refine ⟨153466205010849977989689841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 204621606681133303986253121 153466205010849977989689841)
            ·
              refine ⟨115099653758137483492267381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 153466205010849977989689841 115099653758137483492267381)
              ·
                refine ⟨10790592539825389077400067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 115099653758137483492267381 10790592539825389077400067)
                ·
                  refine ⟨16185888809738083616100101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10790592539825389077400067 16185888809738083616100101)
                  ·
                    refine ⟨3034854151825890678018769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16185888809738083616100101 3034854151825890678018769)
                    ·
                      refine ⟨2276140613869418008514077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3034854151825890678018769 2276140613869418008514077)
                      ·
                        rfl

theorem cell23_4432768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5, 1, 4, 2].length) (baseStart_4432768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4432768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4432768 prefixEnd_4432768 := by exact prefixLift 4432768
  have htrace : WordTrace (prefixWord ++ tailWord_4432768) baseStart_4432768 baseEnd_4432768 := by
    simpa [prefixWord, tailWord_4432768, baseEnd_4432768] using wordTrace_append hprefix tailTrace_4432768
  have hstable : (prefixWord ++ tailWord_4432768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4432768).length < 2 ^ (prefixWord ++ tailWord_4432768).sum := by decide
  have hdescent : baseEnd_4432768 < baseStart_4432768 := by decide
  rcases family_descends (prefixWord ++ tailWord_4432768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4432771 : List Nat := [1, 1, 1, 3, 4, 1, 2, 2, 2, 1, 5]
def baseStart_4432771 : Nat := 118140960795 + 4432771 * 2 ^ 59
def prefixEnd_4432771 : Nat := 4983230072969 + 3 ^ 40 * 4432771 * 2
def baseEnd_4432771 : Nat := 2276142154311381496776563

theorem tailTrace_4432771 : CollatzResearch.WordTrace tailWord_4432771 prefixEnd_4432771 2276142154311381496776563 := by
  unfold tailWord_4432771
  simp only [CollatzResearch.WordTrace]
  refine ⟨161676440623835198859522167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107784293749223465906348111 161676440623835198859522167)
  ·
    refine ⟨242514660935752798289283251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161676440623835198859522167 242514660935752798289283251)
    ·
      refine ⟨363771991403629197433924877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242514660935752798289283251 363771991403629197433924877)
      ·
        refine ⟨136414496776360949037721829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 363771991403629197433924877 136414496776360949037721829)
        ·
          refine ⟨25577718145567677944572843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 136414496776360949037721829 25577718145567677944572843)
          ·
            refine ⟨38366577218351516916859265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25577718145567677944572843 38366577218351516916859265)
            ·
              refine ⟨28774932913763637687644449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38366577218351516916859265 28774932913763637687644449)
              ·
                refine ⟨21581199685322728265733337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28774932913763637687644449 21581199685322728265733337)
                ·
                  refine ⟨16185899763992046199300003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21581199685322728265733337 16185899763992046199300003)
                  ·
                    refine ⟨24278849645988069298950005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16185899763992046199300003 24278849645988069298950005)
                    ·
                      refine ⟨2276142154311381496776563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24278849645988069298950005 2276142154311381496776563)
                      ·
                        rfl

theorem cell23_4432771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 2, 1, 5].length) (baseStart_4432771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4432771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4432771 prefixEnd_4432771 := by exact prefixLift 4432771
  have htrace : WordTrace (prefixWord ++ tailWord_4432771) baseStart_4432771 baseEnd_4432771 := by
    simpa [prefixWord, tailWord_4432771, baseEnd_4432771] using wordTrace_append hprefix tailTrace_4432771
  have hstable : (prefixWord ++ tailWord_4432771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4432771).length < 2 ^ (prefixWord ++ tailWord_4432771).sum := by decide
  have hdescent : baseEnd_4432771 < baseStart_4432771 := by decide
  rcases family_descends (prefixWord ++ tailWord_4432771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4432788 : List Nat := [2, 4, 2, 1, 1, 1, 3, 1, 2, 1, 5]
def baseStart_4432788 : Nat := 118140960795 + 4432788 * 2 ^ 59
def prefixEnd_4432788 : Nat := 4983230072969 + 3 ^ 40 * 4432788 * 2
def baseEnd_4432788 : Nat := 2276150883482507930263985

theorem tailTrace_4432788 : CollatzResearch.WordTrace tailWord_4432788 prefixEnd_4432788 2276150883482507930263985 := by
  unfold tailWord_4432788
  simp only [CollatzResearch.WordTrace]
  refine ⟨80838530332386805381445509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107784707109849073841927345 80838530332386805381445509)
  ·
    refine ⟨15157224437322526009021033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80838530332386805381445509 15157224437322526009021033)
    ·
      refine ⟨11367918327991894506765775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15157224437322526009021033 11367918327991894506765775)
      ·
        refine ⟨17051877491987841760148663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11367918327991894506765775 17051877491987841760148663)
        ·
          refine ⟨25577816237981762640222995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17051877491987841760148663 25577816237981762640222995)
          ·
            refine ⟨38366724356972643960334493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25577816237981762640222995 38366724356972643960334493)
            ·
              refine ⟨14387521633864741485125435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38366724356972643960334493 14387521633864741485125435)
              ·
                refine ⟨21581282450797112227688153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14387521633864741485125435 21581282450797112227688153)
                ·
                  refine ⟨16185961838097834170766115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21581282450797112227688153 16185961838097834170766115)
                  ·
                    refine ⟨24278942757146751256149173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16185961838097834170766115 24278942757146751256149173)
                    ·
                      refine ⟨2276150883482507930263985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24278942757146751256149173 2276150883482507930263985)
                      ·
                        rfl

theorem cell23_4432788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_4432788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4432788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4432788 prefixEnd_4432788 := by exact prefixLift 4432788
  have htrace : WordTrace (prefixWord ++ tailWord_4432788) baseStart_4432788 baseEnd_4432788 := by
    simpa [prefixWord, tailWord_4432788, baseEnd_4432788] using wordTrace_append hprefix tailTrace_4432788
  have hstable : (prefixWord ++ tailWord_4432788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4432788).length < 2 ^ (prefixWord ++ tailWord_4432788).sum := by decide
  have hdescent : baseEnd_4432788 < baseStart_4432788 := by decide
  rcases family_descends (prefixWord ++ tailWord_4432788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4432802 : List Nat := [3, 3, 1, 2, 2, 1, 2, 1, 4, 2, 2]
def baseStart_4432802 : Nat := 118140960795 + 4432802 * 2 ^ 59
def prefixEnd_4432802 : Nat := 4983230072969 + 3 ^ 40 * 4432802 * 2
def baseEnd_4432802 : Nat := 2276158072211670875488921

theorem tailTrace_4432802 : CollatzResearch.WordTrace tailWord_4432802 prefixEnd_4432802 2276158072211670875488921 := by
  unfold tailWord_4432802
  simp only [CollatzResearch.WordTrace]
  refine ⟨40419392821680722788475165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107785047524481927435933773 40419392821680722788475165)
  ·
    refine ⟨15157272308130271045678187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40419392821680722788475165 15157272308130271045678187)
    ·
      refine ⟨22735908462195406568517281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15157272308130271045678187 22735908462195406568517281)
      ·
        refine ⟨17051931346646554926387961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22735908462195406568517281 17051931346646554926387961)
        ·
          refine ⟨12788948509984916194790971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17051931346646554926387961 12788948509984916194790971)
          ·
            refine ⟨19183422764977374292186457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12788948509984916194790971 19183422764977374292186457)
            ·
              refine ⟨14387567073733030719139843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19183422764977374292186457 14387567073733030719139843)
              ·
                refine ⟨21581350610599546078709765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14387567073733030719139843 21581350610599546078709765)
                ·
                  refine ⟨4046503239487414889758081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21581350610599546078709765 4046503239487414889758081)
                  ·
                    refine ⟨3034877429615561167318561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4046503239487414889758081 3034877429615561167318561)
                    ·
                      refine ⟨2276158072211670875488921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3034877429615561167318561 2276158072211670875488921)
                      ·
                        rfl

theorem cell23_4432802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_4432802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4432802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4432802 prefixEnd_4432802 := by exact prefixLift 4432802
  have htrace : WordTrace (prefixWord ++ tailWord_4432802) baseStart_4432802 baseEnd_4432802 := by
    simpa [prefixWord, tailWord_4432802, baseEnd_4432802] using wordTrace_append hprefix tailTrace_4432802
  have hstable : (prefixWord ++ tailWord_4432802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4432802).length < 2 ^ (prefixWord ++ tailWord_4432802).sum := by decide
  have hdescent : baseEnd_4432802 < baseStart_4432802 := by decide
  rcases family_descends (prefixWord ++ tailWord_4432802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4432813 : List Nat := [1, 5, 2, 3, 2, 1, 2, 1, 2, 1, 3]
def baseStart_4432813 : Nat := 118140960795 + 4432813 * 2 ^ 59
def prefixEnd_4432813 : Nat := 4983230072969 + 3 ^ 40 * 4432813 * 2
def baseEnd_4432813 : Nat := 2276163720498870332451371

theorem tailTrace_4432813 : CollatzResearch.WordTrace tailWord_4432813 prefixEnd_4432813 2276163720498870332451371 := by
  unfold tailWord_4432813
  simp only [CollatzResearch.WordTrace]
  refine ⟨161677972489683040032551093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107785314993122026688367395 161677972489683040032551093)
  ·
    refine ⟨15157309920907785003051665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 161677972489683040032551093 15157309920907785003051665)
    ·
      refine ⟨11367982440680838752288749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15157309920907785003051665 11367982440680838752288749)
      ·
        refine ⟨4262993415255314532108281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11367982440680838752288749 4262993415255314532108281)
        ·
          refine ⟨3197245061441485899081211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4262993415255314532108281 3197245061441485899081211)
          ·
            refine ⟨4795867592162228848621817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3197245061441485899081211 4795867592162228848621817)
            ·
              refine ⟨3596900694121671636466363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4795867592162228848621817 3596900694121671636466363)
              ·
                refine ⟨5395351041182507454699545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3596900694121671636466363 5395351041182507454699545)
                ·
                  refine ⟨4046513280886880591024659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5395351041182507454699545 4046513280886880591024659)
                  ·
                    refine ⟨6069769921330320886536989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4046513280886880591024659 6069769921330320886536989)
                    ·
                      refine ⟨2276163720498870332451371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6069769921330320886536989 2276163720498870332451371)
                      ·
                        rfl

theorem cell23_4432813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_4432813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4432813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4432813 prefixEnd_4432813 := by exact prefixLift 4432813
  have htrace : WordTrace (prefixWord ++ tailWord_4432813) baseStart_4432813 baseEnd_4432813 := by
    simpa [prefixWord, tailWord_4432813, baseEnd_4432813] using wordTrace_append hprefix tailTrace_4432813
  have hstable : (prefixWord ++ tailWord_4432813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4432813).length < 2 ^ (prefixWord ++ tailWord_4432813).sum := by decide
  have hdescent : baseEnd_4432813 < baseStart_4432813 := by decide
  rcases family_descends (prefixWord ++ tailWord_4432813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4432932 : List Nat := [2, 3, 1, 4, 1, 2, 3, 1, 6]
def baseStart_4432932 : Nat := 118140960795 + 4432932 * 2 ^ 59
def prefixEnd_4432932 : Nat := 4983230072969 + 3 ^ 40 * 4432932 * 2
def baseEnd_4432932 : Nat := 252913869410750596318147

theorem tailTrace_4432932 : CollatzResearch.WordTrace tailWord_4432932 prefixEnd_4432932 252913869410750596318147 := by
  unfold tailWord_4432932
  simp only [CollatzResearch.WordTrace]
  refine ⟨80841156388125961678066525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107788208517501282237422033 80841156388125961678066525)
  ·
    refine ⟨30315433645547235629274947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80841156388125961678066525 30315433645547235629274947)
    ·
      refine ⟨45473150468320853443912421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30315433645547235629274947 45473150468320853443912421)
      ·
        refine ⟨8526215712810160020733579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45473150468320853443912421 8526215712810160020733579)
        ·
          refine ⟨12789323569215240031100369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8526215712810160020733579 12789323569215240031100369)
          ·
            refine ⟨9591992676911430023325277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12789323569215240031100369 9591992676911430023325277)
            ·
              refine ⟨3596997253841786258746979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9591992676911430023325277 3596997253841786258746979)
              ·
                refine ⟨5395495880762679388120469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3596997253841786258746979 5395495880762679388120469)
                ·
                  refine ⟨252913869410750596318147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5395495880762679388120469 252913869410750596318147)
                  ·
                    rfl

theorem cell23_4432932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3, 1, 6].length) (baseStart_4432932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4432932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4432932 prefixEnd_4432932 := by exact prefixLift 4432932
  have htrace : WordTrace (prefixWord ++ tailWord_4432932) baseStart_4432932 baseEnd_4432932 := by
    simpa [prefixWord, tailWord_4432932, baseEnd_4432932] using wordTrace_append hprefix tailTrace_4432932
  have hstable : (prefixWord ++ tailWord_4432932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4432932).length < 2 ^ (prefixWord ++ tailWord_4432932).sum := by decide
  have hdescent : baseEnd_4432932 < baseStart_4432932 := by decide
  rcases family_descends (prefixWord ++ tailWord_4432932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4432942 : List Nat := [4, 1, 3, 1, 1, 1, 1, 4, 3, 1, 3]
def baseStart_4432942 : Nat := 118140960795 + 4432942 * 2 ^ 59
def prefixEnd_4432942 : Nat := 4983230072969 + 3 ^ 40 * 4432942 * 2
def baseEnd_4432942 : Nat := 2276229959503300327738277

theorem tailTrace_4432942 : CollatzResearch.WordTrace tailWord_4432942 prefixEnd_4432942 2276229959503300327738277 := by
  unfold tailWord_4432942
  simp only [CollatzResearch.WordTrace]
  refine ⟨20210334688276961882999635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107788451670810463375998053 20210334688276961882999635)
  ·
    refine ⟨30315502032415442824499453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20210334688276961882999635 30315502032415442824499453)
    ·
      refine ⟨11368313262155791059187295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30315502032415442824499453 11368313262155791059187295)
      ·
        refine ⟨17052469893233686588780943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11368313262155791059187295 17052469893233686588780943)
        ·
          refine ⟨25578704839850529883171415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17052469893233686588780943 25578704839850529883171415)
          ·
            refine ⟨38368057259775794824757123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25578704839850529883171415 38368057259775794824757123)
            ·
              refine ⟨57552085889663692237135685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38368057259775794824757123 57552085889663692237135685)
              ·
                refine ⟨10791016104311942294462941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57552085889663692237135685 10791016104311942294462941)
                ·
                  refine ⟨4046631039116978360423603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10791016104311942294462941 4046631039116978360423603)
                  ·
                    refine ⟨6069946558675467540635405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4046631039116978360423603 6069946558675467540635405)
                    ·
                      refine ⟨2276229959503300327738277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6069946558675467540635405 2276229959503300327738277)
                      ·
                        rfl

theorem cell23_4432942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_4432942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4432942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4432942 prefixEnd_4432942 := by exact prefixLift 4432942
  have htrace : WordTrace (prefixWord ++ tailWord_4432942) baseStart_4432942 baseEnd_4432942 := by
    simpa [prefixWord, tailWord_4432942, baseEnd_4432942] using wordTrace_append hprefix tailTrace_4432942
  have hstable : (prefixWord ++ tailWord_4432942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4432942).length < 2 ^ (prefixWord ++ tailWord_4432942).sum := by decide
  have hdescent : baseEnd_4432942 < baseStart_4432942 := by decide
  rcases family_descends (prefixWord ++ tailWord_4432942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4432945 : List Nat := [1, 2, 2, 3, 1, 2, 4, 2, 1, 5]
def baseStart_4432945 : Nat := 118140960795 + 4432945 * 2 ^ 59
def prefixEnd_4432945 : Nat := 4983230072969 + 3 ^ 40 * 4432945 * 2
def baseEnd_4432945 : Nat := 758743833315087938666921

theorem tailTrace_4432945 : CollatzResearch.WordTrace tailWord_4432945 prefixEnd_4432945 758743833315087938666921 := by
  unfold tailWord_4432945
  simp only [CollatzResearch.WordTrace]
  refine ⟨161682786925204826576356289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107788524616803217717570859 161682786925204826576356289)
  ·
    refine ⟨121262090193903619932267217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161682786925204826576356289 121262090193903619932267217)
    ·
      refine ⟨90946567645427714949200413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121262090193903619932267217 90946567645427714949200413)
      ·
        refine ⟨34104962867035393105950155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90946567645427714949200413 34104962867035393105950155)
        ·
          refine ⟨51157444300553089658925233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34104962867035393105950155 51157444300553089658925233)
          ·
            refine ⟨38368083225414817244193925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51157444300553089658925233 38368083225414817244193925)
            ·
              refine ⟨7194015604765278233286361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38368083225414817244193925 7194015604765278233286361)
              ·
                refine ⟨5395511703573958674964771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7194015604765278233286361 5395511703573958674964771)
                ·
                  refine ⟨8093267555360938012447157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5395511703573958674964771 8093267555360938012447157)
                  ·
                    refine ⟨758743833315087938666921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8093267555360938012447157 758743833315087938666921)
                    ·
                      rfl

theorem cell23_4432945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 2, 1, 5].length) (baseStart_4432945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4432945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4432945 prefixEnd_4432945 := by exact prefixLift 4432945
  have htrace : WordTrace (prefixWord ++ tailWord_4432945) baseStart_4432945 baseEnd_4432945 := by
    simpa [prefixWord, tailWord_4432945, baseEnd_4432945] using wordTrace_append hprefix tailTrace_4432945
  have hstable : (prefixWord ++ tailWord_4432945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4432945).length < 2 ^ (prefixWord ++ tailWord_4432945).sum := by decide
  have hdescent : baseEnd_4432945 < baseStart_4432945 := by decide
  rcases family_descends (prefixWord ++ tailWord_4432945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4432965 : List Nat := [1, 3, 1, 1, 1, 3, 4, 3, 1, 1, 4]
def baseStart_4432965 : Nat := 118140960795 + 4432965 * 2 ^ 59
def prefixEnd_4432965 : Nat := 4983230072969 + 3 ^ 40 * 4432965 * 2
def baseEnd_4432965 : Nat := 2276241769558353737750671

theorem tailTrace_4432965 : CollatzResearch.WordTrace tailWord_4432965 prefixEnd_4432965 2276241769558353737750671 := by
  unfold tailWord_4432965
  simp only [CollatzResearch.WordTrace]
  refine ⟨161683516385132369992084349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107789010923421579994722899 161683516385132369992084349)
  ·
    refine ⟨60631318644424638747031631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161683516385132369992084349 60631318644424638747031631)
    ·
      refine ⟨90946977966636958120547447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60631318644424638747031631 90946977966636958120547447)
      ·
        refine ⟨136420466949955437180821171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90946977966636958120547447 136420466949955437180821171)
        ·
          refine ⟨204630700424933155771231757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136420466949955437180821171 204630700424933155771231757)
          ·
            refine ⟨76736512659349933414211909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 204630700424933155771231757 76736512659349933414211909)
            ·
              refine ⟨14388096123628112515164733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76736512659349933414211909 14388096123628112515164733)
              ·
                refine ⟨5395536046360542193186775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14388096123628112515164733 5395536046360542193186775)
                ·
                  refine ⟨8093304069540813289780163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5395536046360542193186775 8093304069540813289780163)
                  ·
                    refine ⟨12139956104311219934670245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8093304069540813289780163 12139956104311219934670245)
                    ·
                      refine ⟨2276241769558353737750671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12139956104311219934670245 2276241769558353737750671)
                      ·
                        rfl

theorem cell23_4432965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 3, 1, 1, 4].length) (baseStart_4432965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4432965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4432965 prefixEnd_4432965 := by exact prefixLift 4432965
  have htrace : WordTrace (prefixWord ++ tailWord_4432965) baseStart_4432965 baseEnd_4432965 := by
    simpa [prefixWord, tailWord_4432965, baseEnd_4432965] using wordTrace_append hprefix tailTrace_4432965
  have hstable : (prefixWord ++ tailWord_4432965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4432965).length < 2 ^ (prefixWord ++ tailWord_4432965).sum := by decide
  have hdescent : baseEnd_4432965 < baseStart_4432965 := by decide
  rcases family_descends (prefixWord ++ tailWord_4432965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4433002 : List Nat := [3, 1, 3, 2, 2, 2, 1, 1, 3, 2, 3]
def baseStart_4433002 : Nat := 118140960795 + 4433002 * 2 ^ 59
def prefixEnd_4433002 : Nat := 4983230072969 + 3 ^ 40 * 4433002 * 2
def baseEnd_4433002 : Nat := 2276260768342570092988001

theorem tailTrace_4433002 : CollatzResearch.WordTrace tailWord_4433002 prefixEnd_4433002 2276260768342570092988001 := by
  unfold tailWord_4433002
  simp only [CollatzResearch.WordTrace]
  refine ⟨40421216471499581327795315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107789910590665550207454173 40421216471499581327795315)
  ·
    refine ⟨60631824707249371991692973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40421216471499581327795315 60631824707249371991692973)
    ·
      refine ⟨22736934265218514496884865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60631824707249371991692973 22736934265218514496884865)
      ·
        refine ⟨17052700698913885872663649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22736934265218514496884865 17052700698913885872663649)
        ·
          refine ⟨12789525524185414404497737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17052700698913885872663649 12789525524185414404497737)
          ·
            refine ⟨9592144143139060803373303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12789525524185414404497737 9592144143139060803373303)
            ·
              refine ⟨14388216214708591205059955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9592144143139060803373303 14388216214708591205059955)
              ·
                refine ⟨21582324322062886807589933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14388216214708591205059955 21582324322062886807589933)
                ·
                  refine ⟨8093371620773582552846225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21582324322062886807589933 8093371620773582552846225)
                  ·
                    refine ⟨6070028715580186914634669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8093371620773582552846225 6070028715580186914634669)
                    ·
                      refine ⟨2276260768342570092988001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6070028715580186914634669 2276260768342570092988001)
                      ·
                        rfl

theorem cell23_4433002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_4433002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4433002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4433002 prefixEnd_4433002 := by exact prefixLift 4433002
  have htrace : WordTrace (prefixWord ++ tailWord_4433002) baseStart_4433002 baseEnd_4433002 := by
    simpa [prefixWord, tailWord_4433002, baseEnd_4433002] using wordTrace_append hprefix tailTrace_4433002
  have hstable : (prefixWord ++ tailWord_4433002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4433002).length < 2 ^ (prefixWord ++ tailWord_4433002).sum := by decide
  have hdescent : baseEnd_4433002 < baseStart_4433002 := by decide
  rcases family_descends (prefixWord ++ tailWord_4433002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4433015 : List Nat := [1, 1, 3, 1, 1, 4, 3, 2, 1, 3, 3]
def baseStart_4433015 : Nat := 118140960795 + 4433015 * 2 ^ 59
def prefixEnd_4433015 : Nat := 4983230072969 + 3 ^ 40 * 4433015 * 2
def baseEnd_4433015 : Nat := 2276267443591078542125441

theorem tailTrace_4433015 : CollatzResearch.WordTrace tailWord_4433015 prefixEnd_4433015 2276267443591078542125441 := by
  unfold tailWord_4433015
  simp only [CollatzResearch.WordTrace]
  refine ⟨161685340034951228531404499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107790226689967485687602999 161685340034951228531404499)
  ·
    refine ⟨242528010052426842797106749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161685340034951228531404499 242528010052426842797106749)
    ·
      refine ⟨90948003769660066048915031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 242528010052426842797106749 90948003769660066048915031)
      ·
        refine ⟨136422005654490099073372547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90948003769660066048915031 136422005654490099073372547)
        ·
          refine ⟨204633008481735148610058821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136422005654490099073372547 204633008481735148610058821)
          ·
            refine ⟨38368689090325340364386029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 204633008481735148610058821 38368689090325340364386029)
            ·
              refine ⟨14388258408872002636644761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38368689090325340364386029 14388258408872002636644761)
              ·
                refine ⟨10791193806654001977483571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14388258408872002636644761 10791193806654001977483571)
                ·
                  refine ⟨16186790709981002966225357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10791193806654001977483571 16186790709981002966225357)
                  ·
                    refine ⟨6070046516242876112334509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16186790709981002966225357 6070046516242876112334509)
                    ·
                      refine ⟨2276267443591078542125441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6070046516242876112334509 2276267443591078542125441)
                      ·
                        rfl

theorem cell23_4433015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 2, 1, 3, 3].length) (baseStart_4433015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4433015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4433015 prefixEnd_4433015 := by exact prefixLift 4433015
  have htrace : WordTrace (prefixWord ++ tailWord_4433015) baseStart_4433015 baseEnd_4433015 := by
    simpa [prefixWord, tailWord_4433015, baseEnd_4433015] using wordTrace_append hprefix tailTrace_4433015
  have hstable : (prefixWord ++ tailWord_4433015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4433015).length < 2 ^ (prefixWord ++ tailWord_4433015).sum := by decide
  have hdescent : baseEnd_4433015 < baseStart_4433015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4433015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4433022 : List Nat := [4, 2, 4, 1, 12]
def baseStart_4433022 : Nat := 118140960795 + 4433022 * 2 ^ 59
def prefixEnd_4433022 : Nat := 4983230072969 + 3 ^ 40 * 4433022 * 2
def baseEnd_4433022 : Nat := 3122456842188834039421

theorem tailTrace_4433022 : CollatzResearch.WordTrace tailWord_4433022 prefixEnd_4433022 3122456842188834039421 := by
  unfold tailWord_4433022
  simp only [CollatzResearch.WordTrace]
  refine ⟨20210699418240733590863665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107790396897283912484606213 20210699418240733590863665)
  ·
    refine ⟨15158024563680550193147749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20210699418240733590863665 15158024563680550193147749)
    ·
      refine ⟨2842129605690103161215203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15158024563680550193147749 2842129605690103161215203)
      ·
        refine ⟨4263194408535154741822805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2842129605690103161215203 4263194408535154741822805)
        ·
          refine ⟨3122456842188834039421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 4263194408535154741822805 3122456842188834039421)
          ·
            rfl

theorem cell23_4433022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 12].length) (baseStart_4433022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4433022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4433022 prefixEnd_4433022 := by exact prefixLift 4433022
  have htrace : WordTrace (prefixWord ++ tailWord_4433022) baseStart_4433022 baseEnd_4433022 := by
    simpa [prefixWord, tailWord_4433022, baseEnd_4433022] using wordTrace_append hprefix tailTrace_4433022
  have hstable : (prefixWord ++ tailWord_4433022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4433022).length < 2 ^ (prefixWord ++ tailWord_4433022).sum := by decide
  have hdescent : baseEnd_4433022 < baseStart_4433022 := by decide
  rcases family_descends (prefixWord ++ tailWord_4433022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4433033 : List Nat := [1, 2, 1, 1, 4, 5, 2, 2, 1, 2, 2]
def baseStart_4433033 : Nat := 118140960795 + 4433033 * 2 ^ 59
def prefixEnd_4433033 : Nat := 4983230072969 + 3 ^ 40 * 4433033 * 2
def baseEnd_4433033 : Nat := 2276276686242859471700359

theorem tailTrace_4433033 : CollatzResearch.WordTrace tailWord_4433033 prefixEnd_4433033 2276276686242859471700359 := by
  unfold tailWord_4433033
  simp only [CollatzResearch.WordTrace]
  refine ⟨161685996548886017605559753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107790664365924011737039835 161685996548886017605559753)
  ·
    refine ⟨121264497411664513204169815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161685996548886017605559753 121264497411664513204169815)
    ·
      refine ⟨181896746117496769806254723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121264497411664513204169815 181896746117496769806254723)
      ·
        refine ⟨272845119176245154709382085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181896746117496769806254723 272845119176245154709382085)
        ·
          refine ⟨51158459845545966508009141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 272845119176245154709382085 51158459845545966508009141)
          ·
            refine ⟨4796105610519934360125857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51158459845545966508009141 4796105610519934360125857)
            ·
              refine ⟨3597079207889950770094393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4796105610519934360125857 3597079207889950770094393)
              ·
                refine ⟨2697809405917463077570795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3597079207889950770094393 2697809405917463077570795)
                ·
                  refine ⟨4046714108876194616356193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2697809405917463077570795 4046714108876194616356193)
                  ·
                    refine ⟨3035035581657145962267145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4046714108876194616356193 3035035581657145962267145)
                    ·
                      refine ⟨2276276686242859471700359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3035035581657145962267145 2276276686242859471700359)
                      ·
                        rfl

theorem cell23_4433033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2, 2, 1, 2, 2].length) (baseStart_4433033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4433033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4433033 prefixEnd_4433033 := by exact prefixLift 4433033
  have htrace : WordTrace (prefixWord ++ tailWord_4433033) baseStart_4433033 baseEnd_4433033 := by
    simpa [prefixWord, tailWord_4433033, baseEnd_4433033] using wordTrace_append hprefix tailTrace_4433033
  have hstable : (prefixWord ++ tailWord_4433033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4433033).length < 2 ^ (prefixWord ++ tailWord_4433033).sum := by decide
  have hdescent : baseEnd_4433033 < baseStart_4433033 := by decide
  rcases family_descends (prefixWord ++ tailWord_4433033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4433072 : List Nat := [2, 1, 1, 1, 2, 1, 2, 3, 6, 2, 2]
def baseStart_4433072 : Nat := 118140960795 + 4433072 * 2 ^ 59
def prefixEnd_4433072 : Nat := 4983230072969 + 3 ^ 40 * 4433072 * 2
def baseEnd_4433072 : Nat := 2276296711988384819112679

theorem tailTrace_4433072 : CollatzResearch.WordTrace tailWord_4433072 prefixEnd_4433072 2276296711988384819112679 := by
  unfold tailWord_4433072
  simp only [CollatzResearch.WordTrace]
  refine ⟨80843709497872363633114735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107791612663829818177486313 80843709497872363633114735)
  ·
    refine ⟨121265564246808545449672103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80843709497872363633114735 121265564246808545449672103)
    ·
      refine ⟨181898346370212818174508155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121265564246808545449672103 181898346370212818174508155)
      ·
        refine ⟨272847519555319227261762233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181898346370212818174508155 272847519555319227261762233)
        ·
          refine ⟨204635639666489420446321675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 272847519555319227261762233 204635639666489420446321675)
          ·
            refine ⟨306953459499734130669482513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204635639666489420446321675 306953459499734130669482513)
            ·
              refine ⟨230215094624800598002111885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 306953459499734130669482513 230215094624800598002111885)
              ·
                refine ⟨86330660484300224250791957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 230215094624800598002111885 86330660484300224250791957)
                ·
                  refine ⟨4046749710201573011755873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 86330660484300224250791957 4046749710201573011755873)
                  ·
                    refine ⟨3035062282651179758816905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4046749710201573011755873 3035062282651179758816905)
                    ·
                      refine ⟨2276296711988384819112679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3035062282651179758816905 2276296711988384819112679)
                      ·
                        rfl

theorem cell23_4433072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 6, 2, 2].length) (baseStart_4433072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4433072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4433072 prefixEnd_4433072 := by exact prefixLift 4433072
  have htrace : WordTrace (prefixWord ++ tailWord_4433072) baseStart_4433072 baseEnd_4433072 := by
    simpa [prefixWord, tailWord_4433072, baseEnd_4433072] using wordTrace_append hprefix tailTrace_4433072
  have hstable : (prefixWord ++ tailWord_4433072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4433072).length < 2 ^ (prefixWord ++ tailWord_4433072).sum := by decide
  have hdescent : baseEnd_4433072 < baseStart_4433072 := by decide
  rcases family_descends (prefixWord ++ tailWord_4433072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4433085 : List Nat := [1, 4, 1, 2, 1, 1, 3, 2, 2, 2, 4]
def baseStart_4433085 : Nat := 118140960795 + 4433085 * 2 ^ 59
def prefixEnd_4433085 : Nat := 4983230072969 + 3 ^ 40 * 4433085 * 2
def baseEnd_4433085 : Nat := 2276303387236893268250119

theorem tailTrace_4433085 : CollatzResearch.WordTrace tailWord_4433085 prefixEnd_4433085 2276303387236893268250119 := by
  unfold tailWord_4433085
  simp only [CollatzResearch.WordTrace]
  refine ⟨161687893144697630486452709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107791928763131753657635139 161687893144697630486452709)
  ·
    refine ⟨30316479964630805716209883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 161687893144697630486452709 30316479964630805716209883)
    ·
      refine ⟨45474719946946208574314825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30316479964630805716209883 45474719946946208574314825)
      ·
        refine ⟨34106039960209656430736119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45474719946946208574314825 34106039960209656430736119)
        ·
          refine ⟨51159059940314484646104179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34106039960209656430736119 51159059940314484646104179)
          ·
            refine ⟨76738589910471726969156269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51159059940314484646104179 76738589910471726969156269)
            ·
              refine ⟨28776971216426897613433601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76738589910471726969156269 28776971216426897613433601)
              ·
                refine ⟨21582728412320173210075201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28776971216426897613433601 21582728412320173210075201)
                ·
                  refine ⟨16187046309240129907556401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21582728412320173210075201 16187046309240129907556401)
                  ·
                    refine ⟨12140284731930097430667301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16187046309240129907556401 12140284731930097430667301)
                    ·
                      refine ⟨2276303387236893268250119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12140284731930097430667301 2276303387236893268250119)
                      ·
                        rfl

theorem cell23_4433085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_4433085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4433085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4433085 prefixEnd_4433085 := by exact prefixLift 4433085
  have htrace : WordTrace (prefixWord ++ tailWord_4433085) baseStart_4433085 baseEnd_4433085 := by
    simpa [prefixWord, tailWord_4433085, baseEnd_4433085] using wordTrace_append hprefix tailTrace_4433085
  have hstable : (prefixWord ++ tailWord_4433085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4433085).length < 2 ^ (prefixWord ++ tailWord_4433085).sum := by decide
  have hdescent : baseEnd_4433085 < baseStart_4433085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4433085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4433162 : List Nat := [3, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2]
def baseStart_4433162 : Nat := 118140960795 + 4433162 * 2 ^ 59
def prefixEnd_4433162 : Nat := 4983230072969 + 3 ^ 40 * 4433162 * 2
def baseEnd_4433162 : Nat := 2276342925247289466987265

theorem tailTrace_4433162 : CollatzResearch.WordTrace tailWord_4433162 prefixEnd_4433162 2276342925247289466987265 := by
  unfold tailWord_4433162
  simp only [CollatzResearch.WordTrace]
  refine ⟨40422675391354668159251435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107793801043612448424670493 40422675391354668159251435)
  ·
    refine ⟨60634013087032002238877153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40422675391354668159251435 60634013087032002238877153)
    ·
      refine ⟨45475509815274001679157865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60634013087032002238877153 45475509815274001679157865)
      ·
        refine ⟨34106632361455501259368399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45475509815274001679157865 34106632361455501259368399)
        ·
          refine ⟨51159948542183251889052599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34106632361455501259368399 51159948542183251889052599)
          ·
            refine ⟨76739922813274877833578899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51159948542183251889052599 76739922813274877833578899)
            ·
              refine ⟨115109884219912316750368349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76739922813274877833578899 115109884219912316750368349)
              ·
                refine ⟨43166206582467118781388131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 115109884219912316750368349 43166206582467118781388131)
                ·
                  refine ⟨64749309873700678172082197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43166206582467118781388131 64749309873700678172082197)
                  ·
                    refine ⟨3035123900329719289316353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 64749309873700678172082197 3035123900329719289316353)
                    ·
                      refine ⟨2276342925247289466987265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3035123900329719289316353 2276342925247289466987265)
                      ·
                        rfl

theorem cell23_4433162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2].length) (baseStart_4433162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4433162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4433162 prefixEnd_4433162 := by exact prefixLift 4433162
  have htrace : WordTrace (prefixWord ++ tailWord_4433162) baseStart_4433162 baseEnd_4433162 := by
    simpa [prefixWord, tailWord_4433162, baseEnd_4433162] using wordTrace_append hprefix tailTrace_4433162
  have hstable : (prefixWord ++ tailWord_4433162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4433162).length < 2 ^ (prefixWord ++ tailWord_4433162).sum := by decide
  have hdescent : baseEnd_4433162 < baseStart_4433162 := by decide
  rcases family_descends (prefixWord ++ tailWord_4433162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4433195 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 3, 7, 3]
def baseStart_4433195 : Nat := 118140960795 + 4433195 * 2 ^ 59
def prefixEnd_4433195 : Nat := 4983230072969 + 3 ^ 40 * 4433195 * 2
def baseEnd_4433195 : Nat := 2276359870108887837874613

theorem tailTrace_4433195 : CollatzResearch.WordTrace tailWord_4433195 prefixEnd_4433195 2276359870108887837874613 := by
  unfold tailWord_4433195
  simp only [CollatzResearch.WordTrace]
  refine ⟨161691905174299119272957039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107794603449532746181971359 161691905174299119272957039)
  ·
    refine ⟨242537857761448678909435559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161691905174299119272957039 242537857761448678909435559)
    ·
      refine ⟨363806786642173018364153339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242537857761448678909435559 363806786642173018364153339)
      ·
        refine ⟨545710179963259527546230009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 363806786642173018364153339 545710179963259527546230009)
        ·
          refine ⟨409282634972444645659672507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 545710179963259527546230009 409282634972444645659672507)
          ·
            refine ⟨613923952458666968489508761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 409282634972444645659672507 613923952458666968489508761)
            ·
              refine ⟨460442964344000226367131571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 613923952458666968489508761 460442964344000226367131571)
              ·
                refine ⟨690664446516000339550697357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 460442964344000226367131571 690664446516000339550697357)
                ·
                  refine ⟨258999167443500127331511509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 690664446516000339550697357 258999167443500127331511509)
                  ·
                    refine ⟨6070292986957034234332301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 258999167443500127331511509 6070292986957034234332301)
                    ·
                      refine ⟨2276359870108887837874613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6070292986957034234332301 2276359870108887837874613)
                      ·
                        rfl

theorem cell23_4433195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 7, 3].length) (baseStart_4433195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4433195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4433195 prefixEnd_4433195 := by exact prefixLift 4433195
  have htrace : WordTrace (prefixWord ++ tailWord_4433195) baseStart_4433195 baseEnd_4433195 := by
    simpa [prefixWord, tailWord_4433195, baseEnd_4433195] using wordTrace_append hprefix tailTrace_4433195
  have hstable : (prefixWord ++ tailWord_4433195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4433195).length < 2 ^ (prefixWord ++ tailWord_4433195).sum := by decide
  have hdescent : baseEnd_4433195 < baseStart_4433195 := by decide
  rcases family_descends (prefixWord ++ tailWord_4433195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4433202 : List Nat := [3, 2, 1, 1, 4, 1, 1, 4, 6]
def baseStart_4433202 : Nat := 118140960795 + 4433202 * 2 ^ 59
def prefixEnd_4433202 : Nat := 4983230072969 + 3 ^ 40 * 4433202 * 2
def baseEnd_4433202 : Nat := 252929273830385478943009

theorem tailTrace_4433202 : CollatzResearch.WordTrace tailWord_4433202 prefixEnd_4433202 252929273830385478943009 := by
  unfold tailWord_4433202
  simp only [CollatzResearch.WordTrace]
  refine ⟨40423040121318439867115465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107794773656849172978974573 40423040121318439867115465)
  ·
    refine ⟨30317280090988829900336599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40423040121318439867115465 30317280090988829900336599)
    ·
      refine ⟨45475920136483244850504899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30317280090988829900336599 45475920136483244850504899)
      ·
        refine ⟨68213880204724867275757349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45475920136483244850504899 68213880204724867275757349)
        ·
          refine ⟨12790102538385912614204503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68213880204724867275757349 12790102538385912614204503)
          ·
            refine ⟨19185153807578868921306755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12790102538385912614204503 19185153807578868921306755)
            ·
              refine ⟨28777730711368303381960133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19185153807578868921306755 28777730711368303381960133)
              ·
                refine ⟨5395824508381556884117525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28777730711368303381960133 5395824508381556884117525)
                ·
                  refine ⟨252929273830385478943009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5395824508381556884117525 252929273830385478943009)
                  ·
                    rfl

theorem cell23_4433202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 4, 6].length) (baseStart_4433202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4433202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4433202 prefixEnd_4433202 := by exact prefixLift 4433202
  have htrace : WordTrace (prefixWord ++ tailWord_4433202) baseStart_4433202 baseEnd_4433202 := by
    simpa [prefixWord, tailWord_4433202, baseEnd_4433202] using wordTrace_append hprefix tailTrace_4433202
  have hstable : (prefixWord ++ tailWord_4433202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4433202).length < 2 ^ (prefixWord ++ tailWord_4433202).sum := by decide
  have hdescent : baseEnd_4433202 < baseStart_4433202 := by decide
  rcases family_descends (prefixWord ++ tailWord_4433202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4433232 : List Nat := [2, 1, 1, 1, 1, 5, 2, 4, 1, 5]
def baseStart_4433232 : Nat := 118140960795 + 4433232 * 2 ^ 59
def prefixEnd_4433232 : Nat := 4983230072969 + 3 ^ 40 * 4433232 * 2
def baseEnd_4433232 : Nat := 758792956297701397703981

theorem tailTrace_4433232 : CollatzResearch.WordTrace tailWord_4433232 prefixEnd_4433232 758792956297701397703981 := by
  unfold tailWord_4433232
  simp only [CollatzResearch.WordTrace]
  refine ⟨80846627337582537296026975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107795503116776716394702633 80846627337582537296026975)
  ·
    refine ⟨121269941006373805944040463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80846627337582537296026975 121269941006373805944040463)
    ·
      refine ⟨181904911509560708916060695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121269941006373805944040463 181904911509560708916060695)
      ·
        refine ⟨272857367264341063374091043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181904911509560708916060695 272857367264341063374091043)
        ·
          refine ⟨409286050896511595061136565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272857367264341063374091043 409286050896511595061136565)
          ·
            refine ⟨38370567271547962036981553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 409286050896511595061136565 38370567271547962036981553)
            ·
              refine ⟨28777925453660971527736165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38370567271547962036981553 28777925453660971527736165)
              ·
                refine ⟨5395861022561432161450531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28777925453660971527736165 5395861022561432161450531)
                ·
                  refine ⟨8093791533842148242175797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5395861022561432161450531 8093791533842148242175797)
                  ·
                    refine ⟨758792956297701397703981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8093791533842148242175797 758792956297701397703981)
                    ·
                      rfl

theorem cell23_4433232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 4, 1, 5].length) (baseStart_4433232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4433232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4433232 prefixEnd_4433232 := by exact prefixLift 4433232
  have htrace : WordTrace (prefixWord ++ tailWord_4433232) baseStart_4433232 baseEnd_4433232 := by
    simpa [prefixWord, tailWord_4433232, baseEnd_4433232] using wordTrace_append hprefix tailTrace_4433232
  have hstable : (prefixWord ++ tailWord_4433232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4433232).length < 2 ^ (prefixWord ++ tailWord_4433232).sum := by decide
  have hdescent : baseEnd_4433232 < baseStart_4433232 := by decide
  rcases family_descends (prefixWord ++ tailWord_4433232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4433239 : List Nat := [1, 1, 3, 2, 3, 3, 1, 1, 1, 5, 2]
def baseStart_4433239 : Nat := 118140960795 + 4433239 * 2 ^ 59
def prefixEnd_4433239 : Nat := 4983230072969 + 3 ^ 40 * 4433239 * 2
def baseEnd_4433239 : Nat := 2276382463257685665724411

theorem tailTrace_4433239 : CollatzResearch.WordTrace tailWord_4433239 prefixEnd_4433239 2276382463257685665724411 := by
  unfold tailWord_4433239
  simp only [CollatzResearch.WordTrace]
  refine ⟨161693509986139714787558771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107795673324093143191705847 161693509986139714787558771)
  ·
    refine ⟨242540264979209572181338157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161693509986139714787558771 242540264979209572181338157)
    ·
      refine ⟨90952599367203589568001809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 242540264979209572181338157 90952599367203589568001809)
      ·
        refine ⟨68214449525402692176001357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90952599367203589568001809 68214449525402692176001357)
        ·
          refine ⟨25580418572026009566000509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68214449525402692176001357 25580418572026009566000509)
          ·
            refine ⟨9592656964509753587250191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25580418572026009566000509 9592656964509753587250191)
            ·
              refine ⟨14388985446764630380875287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9592656964509753587250191 14388985446764630380875287)
              ·
                refine ⟨21583478170146945571312931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14388985446764630380875287 21583478170146945571312931)
                ·
                  refine ⟨32375217255220418356969397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21583478170146945571312931 32375217255220418356969397)
                  ·
                    refine ⟨3035176617676914220965881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32375217255220418356969397 3035176617676914220965881)
                    ·
                      refine ⟨2276382463257685665724411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3035176617676914220965881 2276382463257685665724411)
                      ·
                        rfl

theorem cell23_4433239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 5, 2].length) (baseStart_4433239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4433239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4433239 prefixEnd_4433239 := by exact prefixLift 4433239
  have htrace : WordTrace (prefixWord ++ tailWord_4433239) baseStart_4433239 baseEnd_4433239 := by
    simpa [prefixWord, tailWord_4433239, baseEnd_4433239] using wordTrace_append hprefix tailTrace_4433239
  have hstable : (prefixWord ++ tailWord_4433239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4433239).length < 2 ^ (prefixWord ++ tailWord_4433239).sum := by decide
  have hdescent : baseEnd_4433239 < baseStart_4433239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4433239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4433275 : List Nat := [1, 1, 1, 1, 1, 6, 2, 10]
def baseStart_4433275 : Nat := 118140960795 + 4433275 * 2 ^ 59
def prefixEnd_4433275 : Nat := 4983230072969 + 3 ^ 40 * 4433275 * 2
def baseEnd_4433275 : Nat := 84311146243009167587935

theorem tailTrace_4433275 : CollatzResearch.WordTrace tailWord_4433275 prefixEnd_4433275 84311146243009167587935 := by
  unfold tailWord_4433275
  simp only [CollatzResearch.WordTrace]
  refine ⟨161694823014009292935869279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107796548676006195290579519 161694823014009292935869279)
  ·
    refine ⟨242542234521013939403803919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161694823014009292935869279 242542234521013939403803919)
    ·
      refine ⟨363813351781520909105705879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242542234521013939403803919 363813351781520909105705879)
      ·
        refine ⟨545720027672281363658558819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 363813351781520909105705879 545720027672281363658558819)
        ·
          refine ⟨818580041508422045487838229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 545720027672281363658558819 818580041508422045487838229)
          ·
            refine ⟨38370939445707283382242417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 818580041508422045487838229 38370939445707283382242417)
            ·
              refine ⟨28778204584280462536681813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38370939445707283382242417 28778204584280462536681813)
              ·
                refine ⟨84311146243009167587935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 28778204584280462536681813 84311146243009167587935)
                ·
                  rfl

theorem cell23_4433275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 10].length) (baseStart_4433275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4433275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4433275 prefixEnd_4433275 := by exact prefixLift 4433275
  have htrace : WordTrace (prefixWord ++ tailWord_4433275) baseStart_4433275 baseEnd_4433275 := by
    simpa [prefixWord, tailWord_4433275, baseEnd_4433275] using wordTrace_append hprefix tailTrace_4433275
  have hstable : (prefixWord ++ tailWord_4433275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4433275).length < 2 ^ (prefixWord ++ tailWord_4433275).sum := by decide
  have hdescent : baseEnd_4433275 < baseStart_4433275 := by decide
  rcases family_descends (prefixWord ++ tailWord_4433275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4433340 : List Nat := [2, 2, 2, 4, 3, 1, 1, 2, 1, 2, 3]
def baseStart_4433340 : Nat := 118140960795 + 4433340 * 2 ^ 59
def prefixEnd_4433340 : Nat := 4983230072969 + 3 ^ 40 * 4433340 * 2
def baseEnd_4433340 : Nat := 2276434324803789770561447

theorem tailTrace_4433340 : CollatzResearch.WordTrace tailWord_4433340 prefixEnd_4433340 2276434324803789770561447 := by
  unfold tailWord_4433340
  simp only [CollatzResearch.WordTrace]
  refine ⟨80848596879386904518492737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107798129172515872691323649 80848596879386904518492737)
  ·
    refine ⟨60636447659540178388869553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80848596879386904518492737 60636447659540178388869553)
    ·
      refine ⟨45477335744655133791652165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60636447659540178388869553 45477335744655133791652165)
      ·
        refine ⟨8527000452122837585934781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45477335744655133791652165 8527000452122837585934781)
        ·
          refine ⟨3197625169546064094725543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8527000452122837585934781 3197625169546064094725543)
          ·
            refine ⟨4796437754319096142088315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3197625169546064094725543 4796437754319096142088315)
            ·
              refine ⟨7194656631478644213132473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4796437754319096142088315 7194656631478644213132473)
              ·
                refine ⟨5395992473608983159849355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7194656631478644213132473 5395992473608983159849355)
                ·
                  refine ⟨8093988710413474739774033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5395992473608983159849355 8093988710413474739774033)
                  ·
                    refine ⟨6070491532810106054830525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8093988710413474739774033 6070491532810106054830525)
                    ·
                      refine ⟨2276434324803789770561447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6070491532810106054830525 2276434324803789770561447)
                      ·
                        rfl

theorem cell23_4433340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_4433340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4433340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4433340 prefixEnd_4433340 := by exact prefixLift 4433340
  have htrace : WordTrace (prefixWord ++ tailWord_4433340) baseStart_4433340 baseEnd_4433340 := by
    simpa [prefixWord, tailWord_4433340, baseEnd_4433340] using wordTrace_append hprefix tailTrace_4433340
  have hstable : (prefixWord ++ tailWord_4433340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4433340).length < 2 ^ (prefixWord ++ tailWord_4433340).sum := by decide
  have hdescent : baseEnd_4433340 < baseStart_4433340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4433340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4433342 : List Nat := [4, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8]
def baseStart_4433342 : Nat := 118140960795 + 4433342 * 2 ^ 59
def prefixEnd_4433342 : Nat := 4983230072969 + 3 ^ 40 * 4433342 * 2
def baseEnd_4433342 : Nat := 2276435351765098762736437

theorem tailTrace_4433342 : CollatzResearch.WordTrace tailWord_4433342 prefixEnd_4433342 2276435351765098762736437 := by
  unfold tailWord_4433342
  simp only [CollatzResearch.WordTrace]
  refine ⟨20212158338095820422319785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107798177803177708919038853 20212158338095820422319785)
  ·
    refine ⟨15159118753571865316739839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20212158338095820422319785 15159118753571865316739839)
    ·
      refine ⟨22738678130357797975109759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15159118753571865316739839 22738678130357797975109759)
      ·
        refine ⟨34108017195536696962664639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22738678130357797975109759 34108017195536696962664639)
        ·
          refine ⟨51162025793305045443996959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34108017195536696962664639 51162025793305045443996959)
          ·
            refine ⟨76743038689957568165995439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51162025793305045443996959 76743038689957568165995439)
            ·
              refine ⟨115114558034936352248993159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76743038689957568165995439 115114558034936352248993159)
              ·
                refine ⟨172671837052404528373489739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115114558034936352248993159 172671837052404528373489739)
                ·
                  refine ⟨259007755578606792560234609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 172671837052404528373489739 259007755578606792560234609)
                  ·
                    refine ⟨194255816683955094420175957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 259007755578606792560234609 194255816683955094420175957)
                    ·
                      refine ⟨2276435351765098762736437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 194255816683955094420175957 2276435351765098762736437)
                      ·
                        rfl

theorem cell23_4433342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_4433342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4433342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4433342 prefixEnd_4433342 := by exact prefixLift 4433342
  have htrace : WordTrace (prefixWord ++ tailWord_4433342) baseStart_4433342 baseEnd_4433342 := by
    simpa [prefixWord, tailWord_4433342, baseEnd_4433342] using wordTrace_append hprefix tailTrace_4433342
  have hstable : (prefixWord ++ tailWord_4433342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4433342).length < 2 ^ (prefixWord ++ tailWord_4433342).sum := by decide
  have hdescent : baseEnd_4433342 < baseStart_4433342 := by decide
  rcases family_descends (prefixWord ++ tailWord_4433342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4433359 : List Nat := [1, 1, 2, 1, 1, 4, 3, 1, 3, 4, 2]
def baseStart_4433359 : Nat := 118140960795 + 4433359 * 2 ^ 59
def prefixEnd_4433359 : Nat := 4983230072969 + 3 ^ 40 * 4433359 * 2
def baseEnd_4433359 : Nat := 2276444080936225196223859

theorem tailTrace_4433359 : CollatzResearch.WordTrace tailWord_4433359 prefixEnd_4433359 2276444080936225196223859 := by
  unfold tailWord_4433359
  simp only [CollatzResearch.WordTrace]
  refine ⟨161697886745704975281927131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107798591163803316854618087 161697886745704975281927131)
  ·
    refine ⟨242546830118557462922890697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161697886745704975281927131 242546830118557462922890697)
    ·
      refine ⟨181910122588918097192168023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 242546830118557462922890697 181910122588918097192168023)
      ·
        refine ⟨272865183883377145788252035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181910122588918097192168023 272865183883377145788252035)
        ·
          refine ⟨409297775825065718682378053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272865183883377145788252035 409297775825065718682378053)
          ·
            refine ⟨76743332967199822252945885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 409297775825065718682378053 76743332967199822252945885)
            ·
              refine ⟨28778749862699933344854707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76743332967199822252945885 28778749862699933344854707)
              ·
                refine ⟨43168124794049900017282061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28778749862699933344854707 43168124794049900017282061)
                ·
                  refine ⟨16188046797768712506480773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43168124794049900017282061 16188046797768712506480773)
                  ·
                    refine ⟨3035258774581633594965145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16188046797768712506480773 3035258774581633594965145)
                    ·
                      refine ⟨2276444080936225196223859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3035258774581633594965145 2276444080936225196223859)
                      ·
                        rfl

theorem cell23_4433359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 3, 4, 2].length) (baseStart_4433359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4433359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4433359 prefixEnd_4433359 := by exact prefixLift 4433359
  have htrace : WordTrace (prefixWord ++ tailWord_4433359) baseStart_4433359 baseEnd_4433359 := by
    simpa [prefixWord, tailWord_4433359, baseEnd_4433359] using wordTrace_append hprefix tailTrace_4433359
  have hstable : (prefixWord ++ tailWord_4433359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4433359).length < 2 ^ (prefixWord ++ tailWord_4433359).sum := by decide
  have hdescent : baseEnd_4433359 < baseStart_4433359 := by decide
  rcases family_descends (prefixWord ++ tailWord_4433359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4433379 : List Nat := [1, 1, 1, 6, 2, 1, 1, 1, 2, 4, 3]
def baseStart_4433379 : Nat := 118140960795 + 4433379 * 2 ^ 59
def prefixEnd_4433379 : Nat := 4983230072969 + 3 ^ 40 * 4433379 * 2
def baseEnd_4433379 : Nat := 2276454350549315117973767

theorem tailTrace_4433379 : CollatzResearch.WordTrace tailWord_4433379 prefixEnd_4433379 2276454350549315117973767 := by
  unfold tailWord_4433379
  simp only [CollatzResearch.WordTrace]
  refine ⟨161698616205632518697655191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107799077470421679131770127 161698616205632518697655191)
  ·
    refine ⟨242547924308448778046482787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161698616205632518697655191 242547924308448778046482787)
    ·
      refine ⟨363821886462673167069724181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242547924308448778046482787 363821886462673167069724181)
      ·
        refine ⟨17054150927937804706393321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 363821886462673167069724181 17054150927937804706393321)
        ·
          refine ⟨12790613195953353529794991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17054150927937804706393321 12790613195953353529794991)
          ·
            refine ⟨19185919793930030294692487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12790613195953353529794991 19185919793930030294692487)
            ·
              refine ⟨28778879690895045442038731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19185919793930030294692487 28778879690895045442038731)
              ·
                refine ⟨43168319536342568163058097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28778879690895045442038731 43168319536342568163058097)
                ·
                  refine ⟨32376239652256926122293573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43168319536342568163058097 32376239652256926122293573)
                  ·
                    refine ⟨6070544934798173647930045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32376239652256926122293573 6070544934798173647930045)
                    ·
                      refine ⟨2276454350549315117973767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6070544934798173647930045 2276454350549315117973767)
                      ·
                        rfl

theorem cell23_4433379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_4433379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4433379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4433379 prefixEnd_4433379 := by exact prefixLift 4433379
  have htrace : WordTrace (prefixWord ++ tailWord_4433379) baseStart_4433379 baseEnd_4433379 := by
    simpa [prefixWord, tailWord_4433379, baseEnd_4433379] using wordTrace_append hprefix tailTrace_4433379
  have hstable : (prefixWord ++ tailWord_4433379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4433379).length < 2 ^ (prefixWord ++ tailWord_4433379).sum := by decide
  have hdescent : baseEnd_4433379 < baseStart_4433379 := by decide
  rcases family_descends (prefixWord ++ tailWord_4433379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4433393 : List Nat := [1, 2, 2, 2, 3, 2, 2, 3, 2, 2, 2]
def baseStart_4433393 : Nat := 118140960795 + 4433393 * 2 ^ 59
def prefixEnd_4433393 : Nat := 4983230072969 + 3 ^ 40 * 4433393 * 2
def baseEnd_4433393 : Nat := 2276461539278478063198703

theorem tailTrace_4433393 : CollatzResearch.WordTrace tailWord_4433393 prefixEnd_4433393 2276461539278478063198703 := by
  unfold tailWord_4433393
  simp only [CollatzResearch.WordTrace]
  refine ⟨161699126827581799088664833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107799417885054532725776555 161699126827581799088664833)
  ·
    refine ⟨121274345120686349316498625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161699126827581799088664833 121274345120686349316498625)
    ·
      refine ⟨90955758840514761987373969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121274345120686349316498625 90955758840514761987373969)
      ·
        refine ⟨68216819130386071490530477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90955758840514761987373969 68216819130386071490530477)
        ·
          refine ⟨25581307173894776808948929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68216819130386071490530477 25581307173894776808948929)
          ·
            refine ⟨19185980380421082606711697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25581307173894776808948929 19185980380421082606711697)
            ·
              refine ⟨14389485285315811955033773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19185980380421082606711697 14389485285315811955033773)
              ·
                refine ⟨5396056981993429483137665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14389485285315811955033773 5396056981993429483137665)
                ·
                  refine ⟨4047042736495072112353249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5396056981993429483137665 4047042736495072112353249)
                  ·
                    refine ⟨3035282052371304084264937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4047042736495072112353249 3035282052371304084264937)
                    ·
                      refine ⟨2276461539278478063198703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3035282052371304084264937 2276461539278478063198703)
                      ·
                        rfl

theorem cell23_4433393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 3, 2, 2, 2].length) (baseStart_4433393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4433393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4433393 prefixEnd_4433393 := by exact prefixLift 4433393
  have htrace : WordTrace (prefixWord ++ tailWord_4433393) baseStart_4433393 baseEnd_4433393 := by
    simpa [prefixWord, tailWord_4433393, baseEnd_4433393] using wordTrace_append hprefix tailTrace_4433393
  have hstable : (prefixWord ++ tailWord_4433393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4433393).length < 2 ^ (prefixWord ++ tailWord_4433393).sum := by decide
  have hdescent : baseEnd_4433393 < baseStart_4433393 := by decide
  rcases family_descends (prefixWord ++ tailWord_4433393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4433414 : List Nat := [6, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2]
def baseStart_4433414 : Nat := 118140960795 + 4433414 * 2 ^ 59
def prefixEnd_4433414 : Nat := 4983230072969 + 3 ^ 40 * 4433414 * 2
def baseEnd_4433414 : Nat := 2276472322372222481036107

theorem tailTrace_4433414 : CollatzResearch.WordTrace tailWord_4433414 prefixEnd_4433414 2276472322372222481036107 := by
  unfold tailWord_4433414
  simp only [CollatzResearch.WordTrace]
  refine ⟨5053121648765803739849353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 107799928507003813116786197 5053121648765803739849353)
  ·
    refine ⟨3789841236574352804887015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5053121648765803739849353 3789841236574352804887015)
    ·
      refine ⟨5684761854861529207330523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3789841236574352804887015 5684761854861529207330523)
      ·
        refine ⟨8527142782292293810995785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5684761854861529207330523 8527142782292293810995785)
        ·
          refine ⟨6395357086719220358246839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8527142782292293810995785 6395357086719220358246839)
          ·
            refine ⟨9593035630078830537370259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6395357086719220358246839 9593035630078830537370259)
            ·
              refine ⟨14389553445118245806055389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9593035630078830537370259 14389553445118245806055389)
              ·
                refine ⟨5396082541919342177270771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14389553445118245806055389 5396082541919342177270771)
                ·
                  refine ⟨8094123812879013265906157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5396082541919342177270771 8094123812879013265906157)
                  ·
                    refine ⟨3035296429829629974714809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8094123812879013265906157 3035296429829629974714809)
                    ·
                      refine ⟨2276472322372222481036107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3035296429829629974714809 2276472322372222481036107)
                      ·
                        rfl

theorem cell23_4433414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_4433414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4433414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4433414 prefixEnd_4433414 := by exact prefixLift 4433414
  have htrace : WordTrace (prefixWord ++ tailWord_4433414) baseStart_4433414 baseEnd_4433414 := by
    simpa [prefixWord, tailWord_4433414, baseEnd_4433414] using wordTrace_append hprefix tailTrace_4433414
  have hstable : (prefixWord ++ tailWord_4433414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4433414).length < 2 ^ (prefixWord ++ tailWord_4433414).sum := by decide
  have hdescent : baseEnd_4433414 < baseStart_4433414 := by decide
  rcases family_descends (prefixWord ++ tailWord_4433414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4433489 : List Nat := [1, 2, 2, 1, 3, 2, 2, 4, 6]
def baseStart_4433489 : Nat := 118140960795 + 4433489 * 2 ^ 59
def prefixEnd_4433489 : Nat := 4983230072969 + 3 ^ 40 * 4433489 * 2
def baseEnd_4433489 : Nat := 252945648157923298622029

theorem tailTrace_4433489 : CollatzResearch.WordTrace tailWord_4433489 prefixEnd_4433489 252945648157923298622029 := by
  unfold tailWord_4433489
  simp only [CollatzResearch.WordTrace]
  refine ⟨161702628235234007484159521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107801752156822671656106347 161702628235234007484159521)
  ·
    refine ⟨121276971176425505613119641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161702628235234007484159521 121276971176425505613119641)
    ·
      refine ⟨90957728382319129209839731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121276971176425505613119641 90957728382319129209839731)
      ·
        refine ⟨136436592573478693814759597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90957728382319129209839731 136436592573478693814759597)
        ·
          refine ⟨51163722215054510180534849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136436592573478693814759597 51163722215054510180534849)
          ·
            refine ⟨38372791661290882635401137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51163722215054510180534849 38372791661290882635401137)
            ·
              refine ⟨28779593745968161976550853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38372791661290882635401137 28779593745968161976550853)
              ·
                refine ⟨5396173827369030370603285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28779593745968161976550853 5396173827369030370603285)
                ·
                  refine ⟨252945648157923298622029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5396173827369030370603285 252945648157923298622029)
                  ·
                    rfl

theorem cell23_4433489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 4, 6].length) (baseStart_4433489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4433489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4433489 prefixEnd_4433489 := by exact prefixLift 4433489
  have htrace : WordTrace (prefixWord ++ tailWord_4433489) baseStart_4433489 baseEnd_4433489 := by
    simpa [prefixWord, tailWord_4433489, baseEnd_4433489] using wordTrace_append hprefix tailTrace_4433489
  have hstable : (prefixWord ++ tailWord_4433489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4433489).length < 2 ^ (prefixWord ++ tailWord_4433489).sum := by decide
  have hdescent : baseEnd_4433489 < baseStart_4433489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4433489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4433516 : List Nat := [2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 3]
def baseStart_4433516 : Nat := 118140960795 + 4433516 * 2 ^ 59
def prefixEnd_4433516 : Nat := 4983230072969 + 3 ^ 40 * 4433516 * 2
def baseEnd_4433516 : Nat := 2276524697398981081960637

theorem tailTrace_4433516 : CollatzResearch.WordTrace tailWord_4433516 prefixEnd_4433516 2276524697398981081960637 := by
  unfold tailWord_4433516
  simp only [CollatzResearch.WordTrace]
  refine ⟨80851806503068095547696201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107802408670757460730261601 80851806503068095547696201)
  ·
    refine ⟨60638854877301071660772151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80851806503068095547696201 60638854877301071660772151)
    ·
      refine ⟨90958282315951607491158227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60638854877301071660772151 90958282315951607491158227)
      ·
        refine ⟨136437423473927411236737341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90958282315951607491158227 136437423473927411236737341)
        ·
          refine ⟨51164033802722779213776503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136437423473927411236737341 51164033802722779213776503)
          ·
            refine ⟨76746050704084168820664755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51164033802722779213776503 76746050704084168820664755)
            ·
              refine ⟨115119076056126253230997133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76746050704084168820664755 115119076056126253230997133)
              ·
                refine ⟨43169653521047344961623925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 115119076056126253230997133 43169653521047344961623925)
                ·
                  refine ⟨4047155017598188590152243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43169653521047344961623925 4047155017598188590152243)
                  ·
                    refine ⟨6070732526397282885228365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4047155017598188590152243 6070732526397282885228365)
                    ·
                      refine ⟨2276524697398981081960637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6070732526397282885228365 2276524697398981081960637)
                      ·
                        rfl

theorem cell23_4433516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 3].length) (baseStart_4433516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4433516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4433516 prefixEnd_4433516 := by exact prefixLift 4433516
  have htrace : WordTrace (prefixWord ++ tailWord_4433516) baseStart_4433516 baseEnd_4433516 := by
    simpa [prefixWord, tailWord_4433516, baseEnd_4433516] using wordTrace_append hprefix tailTrace_4433516
  have hstable : (prefixWord ++ tailWord_4433516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4433516).length < 2 ^ (prefixWord ++ tailWord_4433516).sum := by decide
  have hdescent : baseEnd_4433516 < baseStart_4433516 := by decide
  rcases family_descends (prefixWord ++ tailWord_4433516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4433543 : List Nat := [1, 1, 4, 2, 1, 3, 2, 2, 2, 3, 2]
def baseStart_4433543 : Nat := 118140960795 + 4433543 * 2 ^ 59
def prefixEnd_4433543 : Nat := 4983230072969 + 3 ^ 40 * 4433543 * 2
def baseEnd_4433543 : Nat := 2276538561376652476323013

theorem tailTrace_4433543 : CollatzResearch.WordTrace tailWord_4433543 prefixEnd_4433543 2276538561376652476323013 := by
  unfold tailWord_4433543
  simp only [CollatzResearch.WordTrace]
  refine ⟨161704597777038374706625283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107803065184692249804416855 161704597777038374706625283)
  ·
    refine ⟨242556896665557562059937925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161704597777038374706625283 242556896665557562059937925)
    ·
      refine ⟨45479418124792042886238361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 242556896665557562059937925 45479418124792042886238361)
      ·
        refine ⟨34109563593594032164678771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45479418124792042886238361 34109563593594032164678771)
        ·
          refine ⟨51164345390391048247018157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34109563593594032164678771 51164345390391048247018157)
          ·
            refine ⟨19186629521396643092631809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51164345390391048247018157 19186629521396643092631809)
            ·
              refine ⟨14389972141047482319473857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19186629521396643092631809 14389972141047482319473857)
              ·
                refine ⟨10792479105785611739605393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14389972141047482319473857 10792479105785611739605393)
                ·
                  refine ⟨8094359329339208804704045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10792479105785611739605393 8094359329339208804704045)
                  ·
                    refine ⟨3035384748502203301764017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8094359329339208804704045 3035384748502203301764017)
                    ·
                      refine ⟨2276538561376652476323013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3035384748502203301764017 2276538561376652476323013)
                      ·
                        rfl

theorem cell23_4433543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 2, 2, 3, 2].length) (baseStart_4433543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4433543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4433543 prefixEnd_4433543 := by exact prefixLift 4433543
  have htrace : WordTrace (prefixWord ++ tailWord_4433543) baseStart_4433543 baseEnd_4433543 := by
    simpa [prefixWord, tailWord_4433543, baseEnd_4433543] using wordTrace_append hprefix tailTrace_4433543
  have hstable : (prefixWord ++ tailWord_4433543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4433543).length < 2 ^ (prefixWord ++ tailWord_4433543).sum := by decide
  have hdescent : baseEnd_4433543 < baseStart_4433543 := by decide
  rcases family_descends (prefixWord ++ tailWord_4433543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4433544 : List Nat := [2, 1, 3, 5, 1, 2, 2, 2, 1, 4]
def baseStart_4433544 : Nat := 118140960795 + 4433544 * 2 ^ 59
def prefixEnd_4433544 : Nat := 4983230072969 + 3 ^ 40 * 4433544 * 2
def baseEnd_4433544 : Nat := 758846358285768990803503

theorem tailTrace_4433544 : CollatzResearch.WordTrace tailWord_4433544 prefixEnd_4433544 758846358285768990803503 := by
  unfold tailWord_4433544
  simp only [CollatzResearch.WordTrace]
  refine ⟨80852317125017375938705843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107803089500023167918274457 80852317125017375938705843)
  ·
    refine ⟨121278475687526063908058765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80852317125017375938705843 121278475687526063908058765)
    ·
      refine ⟨45479428382822273965522037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121278475687526063908058765 45479428382822273965522037)
      ·
        refine ⟨4263696410889588184267691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45479428382822273965522037 4263696410889588184267691)
        ·
          refine ⟨6395544616334382276401537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4263696410889588184267691 6395544616334382276401537)
          ·
            refine ⟨4796658462250786707301153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6395544616334382276401537 4796658462250786707301153)
            ·
              refine ⟨3597493846688090030475865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4796658462250786707301153 3597493846688090030475865)
              ·
                refine ⟨2698120385016067522856899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3597493846688090030475865 2698120385016067522856899)
                ·
                  refine ⟨4047180577524101284285349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2698120385016067522856899 4047180577524101284285349)
                  ·
                    refine ⟨758846358285768990803503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4047180577524101284285349 758846358285768990803503)
                    ·
                      rfl

theorem cell23_4433544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2, 2, 1, 4].length) (baseStart_4433544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4433544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4433544 prefixEnd_4433544 := by exact prefixLift 4433544
  have htrace : WordTrace (prefixWord ++ tailWord_4433544) baseStart_4433544 baseEnd_4433544 := by
    simpa [prefixWord, tailWord_4433544, baseEnd_4433544] using wordTrace_append hprefix tailTrace_4433544
  have hstable : (prefixWord ++ tailWord_4433544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4433544).length < 2 ^ (prefixWord ++ tailWord_4433544).sum := by decide
  have hdescent : baseEnd_4433544 < baseStart_4433544 := by decide
  rcases family_descends (prefixWord ++ tailWord_4433544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4433573 : List Nat := [1, 3, 1, 2, 1, 2, 3, 1, 5, 2, 2]
def baseStart_4433573 : Nat := 118140960795 + 4433573 * 2 ^ 59
def prefixEnd_4433573 : Nat := 4983230072969 + 3 ^ 40 * 4433573 * 2
def baseEnd_4433573 : Nat := 2276553965796287358947875

theorem tailTrace_4433573 : CollatzResearch.WordTrace tailWord_4433573 prefixEnd_4433573 2276553965796287358947875 := by
  unfold tailWord_4433573
  simp only [CollatzResearch.WordTrace]
  refine ⟨161705691966929689830217373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107803794644619793220144915 161705691966929689830217373)
  ·
    refine ⟨60639634487598633686331515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161705691966929689830217373 60639634487598633686331515)
    ·
      refine ⟨90959451731397950529497273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60639634487598633686331515 90959451731397950529497273)
      ·
        refine ⟨68219588798548462897122955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90959451731397950529497273 68219588798548462897122955)
        ·
          refine ⟨102329383197822694345684433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68219588798548462897122955 102329383197822694345684433)
          ·
            refine ⟨76747037398367020759263325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102329383197822694345684433 76747037398367020759263325)
            ·
              refine ⟨28780139024387632784723747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76747037398367020759263325 28780139024387632784723747)
              ·
                refine ⟨43170208536581449177085621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28780139024387632784723747 43170208536581449177085621)
                ·
                  refine ⟨4047207050304510860351777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43170208536581449177085621 4047207050304510860351777)
                  ·
                    refine ⟨3035405287728383145263833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4047207050304510860351777 3035405287728383145263833)
                    ·
                      refine ⟨2276553965796287358947875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3035405287728383145263833 2276553965796287358947875)
                      ·
                        rfl

theorem cell23_4433573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 5, 2, 2].length) (baseStart_4433573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4433573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4433573 prefixEnd_4433573 := by exact prefixLift 4433573
  have htrace : WordTrace (prefixWord ++ tailWord_4433573) baseStart_4433573 baseEnd_4433573 := by
    simpa [prefixWord, tailWord_4433573, baseEnd_4433573] using wordTrace_append hprefix tailTrace_4433573
  have hstable : (prefixWord ++ tailWord_4433573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4433573).length < 2 ^ (prefixWord ++ tailWord_4433573).sum := by decide
  have hdescent : baseEnd_4433573 < baseStart_4433573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4433573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4433586 : List Nat := [3, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4]
def baseStart_4433586 : Nat := 118140960795 + 4433586 * 2 ^ 59
def prefixEnd_4433586 : Nat := 4983230072969 + 3 ^ 40 * 4433586 * 2
def baseEnd_4433586 : Nat := 2276560641044795808085315

theorem tailTrace_4433586 : CollatzResearch.WordTrace tailWord_4433586 prefixEnd_4433586 2276560641044795808085315 := by
  unfold tailWord_4433586
  simp only [CollatzResearch.WordTrace]
  refine ⟨40426541528970648262610153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107804110743921728700293741 40426541528970648262610153)
  ·
    refine ⟨30319906146727986196957615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40426541528970648262610153 30319906146727986196957615)
    ·
      refine ⟨45479859220091979295436423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30319906146727986196957615 45479859220091979295436423)
      ·
        refine ⟨68219788830137968943154635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45479859220091979295436423 68219788830137968943154635)
        ·
          refine ⟨102329683245206953414731953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68219788830137968943154635 102329683245206953414731953)
          ·
            refine ⟨76747262433905215061048965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102329683245206953414731953 76747262433905215061048965)
            ·
              refine ⟨14390111706357227823946681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76747262433905215061048965 14390111706357227823946681)
              ·
                refine ⟨10792583779767920867960011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14390111706357227823946681 10792583779767920867960011)
                ·
                  refine ⟨16188875669651881301940017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10792583779767920867960011 16188875669651881301940017)
                  ·
                    refine ⟨12141656752238910976455013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16188875669651881301940017 12141656752238910976455013)
                    ·
                      refine ⟨2276560641044795808085315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12141656752238910976455013 2276560641044795808085315)
                      ·
                        rfl

theorem cell23_4433586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4].length) (baseStart_4433586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4433586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4433586 prefixEnd_4433586 := by exact prefixLift 4433586
  have htrace : WordTrace (prefixWord ++ tailWord_4433586) baseStart_4433586 baseEnd_4433586 := by
    simpa [prefixWord, tailWord_4433586, baseEnd_4433586] using wordTrace_append hprefix tailTrace_4433586
  have hstable : (prefixWord ++ tailWord_4433586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4433586).length < 2 ^ (prefixWord ++ tailWord_4433586).sum := by decide
  have hdescent : baseEnd_4433586 < baseStart_4433586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4433586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4433616 : List Nat := [2, 1, 1, 1, 1, 2, 1, 3, 2, 7, 2]
def baseStart_4433616 : Nat := 118140960795 + 4433616 * 2 ^ 59
def prefixEnd_4433616 : Nat := 4983230072969 + 3 ^ 40 * 4433616 * 2
def baseEnd_4433616 : Nat := 2276576045464430690710177

theorem tailTrace_4433616 : CollatzResearch.WordTrace tailWord_4433616 prefixEnd_4433616 2276576045464430690710177 := by
  unfold tailWord_4433616
  simp only [CollatzResearch.WordTrace]
  refine ⟨80853630152886954087016351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107804840203849272116021801 80853630152886954087016351)
  ·
    refine ⟨121280445229330431130524527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80853630152886954087016351 121280445229330431130524527)
    ·
      refine ⟨181920667843995646695786791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121280445229330431130524527 181920667843995646695786791)
      ·
        refine ⟨272881001765993470043680187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181920667843995646695786791 272881001765993470043680187)
        ·
          refine ⟨409321502648990205065520281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272881001765993470043680187 409321502648990205065520281)
          ·
            refine ⟨306991126986742653799140211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 409321502648990205065520281 306991126986742653799140211)
            ·
              refine ⟨460486690480113980698710317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 306991126986742653799140211 460486690480113980698710317)
              ·
                refine ⟨172682508930042742762016369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 460486690480113980698710317 172682508930042742762016369)
                ·
                  refine ⟨129511881697532057071512277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 172682508930042742762016369 129511881697532057071512277)
                  ·
                    refine ⟨3035434727285907587613569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 129511881697532057071512277 3035434727285907587613569)
                    ·
                      refine ⟨2276576045464430690710177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3035434727285907587613569 2276576045464430690710177)
                      ·
                        rfl

theorem cell23_4433616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 2, 7, 2].length) (baseStart_4433616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4433616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4433616 prefixEnd_4433616 := by exact prefixLift 4433616
  have htrace : WordTrace (prefixWord ++ tailWord_4433616) baseStart_4433616 baseEnd_4433616 := by
    simpa [prefixWord, tailWord_4433616, baseEnd_4433616] using wordTrace_append hprefix tailTrace_4433616
  have hstable : (prefixWord ++ tailWord_4433616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4433616).length < 2 ^ (prefixWord ++ tailWord_4433616).sum := by decide
  have hdescent : baseEnd_4433616 < baseStart_4433616 := by decide
  rcases family_descends (prefixWord ++ tailWord_4433616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4433620 : List Nat := [2, 4, 1, 3, 1, 3, 1, 1, 1, 2, 4]
def baseStart_4433620 : Nat := 118140960795 + 4433620 * 2 ^ 59
def prefixEnd_4433620 : Nat := 4983230072969 + 3 ^ 40 * 4433620 * 2
def baseEnd_4433620 : Nat := 2276578099387048675060159

theorem tailTrace_4433620 : CollatzResearch.WordTrace tailWord_4433620 prefixEnd_4433620 2276578099387048675060159 := by
  unfold tailWord_4433620
  simp only [CollatzResearch.WordTrace]
  refine ⟨80853703098879708428589157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107804937465172944571452209 80853703098879708428589157)
  ·
    refine ⟨15160069331039945330360467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80853703098879708428589157 15160069331039945330360467)
    ·
      refine ⟨22740103996559917995540701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15160069331039945330360467 22740103996559917995540701)
      ·
        refine ⟨8527538998709969248327763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22740103996559917995540701 8527538998709969248327763)
        ·
          refine ⟨12791308498064953872491645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8527538998709969248327763 12791308498064953872491645)
          ·
            refine ⟨4796740686774357702184367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12791308498064953872491645 4796740686774357702184367)
            ·
              refine ⟨7195111030161536553276551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4796740686774357702184367 7195111030161536553276551)
              ·
                refine ⟨10792666545242304829914827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7195111030161536553276551 10792666545242304829914827)
                ·
                  refine ⟨16188999817863457244872241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10792666545242304829914827 16188999817863457244872241)
                  ·
                    refine ⟨12141749863397592933654181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16188999817863457244872241 12141749863397592933654181)
                    ·
                      refine ⟨2276578099387048675060159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12141749863397592933654181 2276578099387048675060159)
                      ·
                        rfl

theorem cell23_4433620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_4433620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4433620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4433620 prefixEnd_4433620 := by exact prefixLift 4433620
  have htrace : WordTrace (prefixWord ++ tailWord_4433620) baseStart_4433620 baseEnd_4433620 := by
    simpa [prefixWord, tailWord_4433620, baseEnd_4433620] using wordTrace_append hprefix tailTrace_4433620
  have hstable : (prefixWord ++ tailWord_4433620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4433620).length < 2 ^ (prefixWord ++ tailWord_4433620).sum := by decide
  have hdescent : baseEnd_4433620 < baseStart_4433620 := by decide
  rcases family_descends (prefixWord ++ tailWord_4433620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4433650 : List Nat := [3, 2, 1, 3, 1, 1, 1, 5, 1, 3, 2]
def baseStart_4433650 : Nat := 118140960795 + 4433650 * 2 ^ 59
def prefixEnd_4433650 : Nat := 4983230072969 + 3 ^ 40 * 4433650 * 2
def baseEnd_4433650 : Nat := 2276593503806683557685021

theorem tailTrace_4433650 : CollatzResearch.WordTrace tailWord_4433650 prefixEnd_4433650 2276593503806683557685021 := by
  unfold tailWord_4433650
  simp only [CollatzResearch.WordTrace]
  refine ⟨40427125096912682995192601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107805666925100487987180269 40427125096912682995192601)
  ·
    refine ⟨30320343822684512246394451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40427125096912682995192601 30320343822684512246394451)
    ·
      refine ⟨45480515734026768369591677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30320343822684512246394451 45480515734026768369591677)
      ·
        refine ⟨17055193400260038138596879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45480515734026768369591677 17055193400260038138596879)
        ·
          refine ⟨25582790100390057207895319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17055193400260038138596879 25582790100390057207895319)
          ·
            refine ⟨38374185150585085811842979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25582790100390057207895319 38374185150585085811842979)
            ·
              refine ⟨57561277725877628717764469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38374185150585085811842979 57561277725877628717764469)
              ·
                refine ⟨5396369786801027692290419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57561277725877628717764469 5396369786801027692290419)
                ·
                  refine ⟨8094554680201541538435629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5396369786801027692290419 8094554680201541538435629)
                  ·
                    refine ⟨3035458005075578076913361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8094554680201541538435629 3035458005075578076913361)
                    ·
                      refine ⟨2276593503806683557685021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3035458005075578076913361 2276593503806683557685021)
                      ·
                        rfl

theorem cell23_4433650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_4433650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4433650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4433650 prefixEnd_4433650 := by exact prefixLift 4433650
  have htrace : WordTrace (prefixWord ++ tailWord_4433650) baseStart_4433650 baseEnd_4433650 := by
    simpa [prefixWord, tailWord_4433650, baseEnd_4433650] using wordTrace_append hprefix tailTrace_4433650
  have hstable : (prefixWord ++ tailWord_4433650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4433650).length < 2 ^ (prefixWord ++ tailWord_4433650).sum := by decide
  have hdescent : baseEnd_4433650 < baseStart_4433650 := by decide
  rcases family_descends (prefixWord ++ tailWord_4433650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4433659 : List Nat := [1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 6]
def baseStart_4433659 : Nat := 118140960795 + 4433659 * 2 ^ 59
def prefixEnd_4433659 : Nat := 4983230072969 + 3 ^ 40 * 4433659 * 2
def baseEnd_4433659 : Nat := 2276598125132574022472479

theorem tailTrace_4433659 : CollatzResearch.WordTrace tailWord_4433659 prefixEnd_4433659 2276598125132574022472479 := by
  unfold tailWord_4433659
  simp only [CollatzResearch.WordTrace]
  refine ⟨161708828644618126517848031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107805885763078751011898687 161708828644618126517848031)
  ·
    refine ⟨242563242966927189776772047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161708828644618126517848031 242563242966927189776772047)
    ·
      refine ⟨363844864450390784665158071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242563242966927189776772047 363844864450390784665158071)
      ·
        refine ⟨545767296675586176997737107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 363844864450390784665158071 545767296675586176997737107)
        ·
          refine ⟨818650945013379265496605661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 545767296675586176997737107 818650945013379265496605661)
          ·
            refine ⟨306994104380017224561227123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 818650945013379265496605661 306994104380017224561227123)
            ·
              refine ⟨460491156570025836841840685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 306994104380017224561227123 460491156570025836841840685)
              ·
                refine ⟨172684183713759688815690257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 460491156570025836841840685 172684183713759688815690257)
                ·
                  refine ⟨129513137785319766611767693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 172684183713759688815690257 129513137785319766611767693)
                  ·
                    refine ⟨48567426669494912479412885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 129513137785319766611767693 48567426669494912479412885)
                    ·
                      refine ⟨2276598125132574022472479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48567426669494912479412885 2276598125132574022472479)
                      ·
                        rfl

theorem cell23_4433659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 6].length) (baseStart_4433659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4433659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4433659 prefixEnd_4433659 := by exact prefixLift 4433659
  have htrace : WordTrace (prefixWord ++ tailWord_4433659) baseStart_4433659 baseEnd_4433659 := by
    simpa [prefixWord, tailWord_4433659, baseEnd_4433659] using wordTrace_append hprefix tailTrace_4433659
  have hstable : (prefixWord ++ tailWord_4433659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4433659).length < 2 ^ (prefixWord ++ tailWord_4433659).sum := by decide
  have hdescent : baseEnd_4433659 < baseStart_4433659 := by decide
  rcases family_descends (prefixWord ++ tailWord_4433659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4433676 : List Nat := [2, 2, 1, 2, 2, 1, 2, 3, 2, 2, 4]
def baseStart_4433676 : Nat := 118140960795 + 4433676 * 2 ^ 59
def prefixEnd_4433676 : Nat := 4983230072969 + 3 ^ 40 * 4433676 * 2
def baseEnd_4433676 : Nat := 2276606854303700455959901

theorem tailTrace_4433676 : CollatzResearch.WordTrace tailWord_4433676 prefixEnd_4433676 2276606854303700455959901 := by
  unfold tailWord_4433676
  simp only [CollatzResearch.WordTrace]
  refine ⟨80854724342778269210608441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107806299123704358947477921 80854724342778269210608441)
  ·
    refine ⟨60641043257083701907956331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80854724342778269210608441 60641043257083701907956331)
    ·
      refine ⟨90961564885625552861934497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60641043257083701907956331 90961564885625552861934497)
      ·
        refine ⟨68221173664219164646450873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90961564885625552861934497 68221173664219164646450873)
        ·
          refine ⟨51165880248164373484838155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68221173664219164646450873 51165880248164373484838155)
          ·
            refine ⟨76748820372246560227257233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51165880248164373484838155 76748820372246560227257233)
            ·
              refine ⟨57561615279184920170442925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76748820372246560227257233 57561615279184920170442925)
              ·
                refine ⟨21585605729694345063916097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57561615279184920170442925 21585605729694345063916097)
                ·
                  refine ⟨16189204297270758797937073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21585605729694345063916097 16189204297270758797937073)
                  ·
                    refine ⟨12141903222953069098452805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16189204297270758797937073 12141903222953069098452805)
                    ·
                      refine ⟨2276606854303700455959901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12141903222953069098452805 2276606854303700455959901)
                      ·
                        rfl

theorem cell23_4433676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_4433676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4433676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4433676 prefixEnd_4433676 := by exact prefixLift 4433676
  have htrace : WordTrace (prefixWord ++ tailWord_4433676) baseStart_4433676 baseEnd_4433676 := by
    simpa [prefixWord, tailWord_4433676, baseEnd_4433676] using wordTrace_append hprefix tailTrace_4433676
  have hstable : (prefixWord ++ tailWord_4433676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4433676).length < 2 ^ (prefixWord ++ tailWord_4433676).sum := by decide
  have hdescent : baseEnd_4433676 < baseStart_4433676 := by decide
  rcases family_descends (prefixWord ++ tailWord_4433676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4433720 : List Nat := [2, 1, 2, 1, 3, 3, 4, 2, 5]
def baseStart_4433720 : Nat := 118140960795 + 4433720 * 2 ^ 59
def prefixEnd_4433720 : Nat := 4983230072969 + 3 ^ 40 * 4433720 * 2
def baseEnd_4433720 : Nat := 252958827494722031534411

theorem tailTrace_4433720 : CollatzResearch.WordTrace tailWord_4433720 prefixEnd_4433720 252958827494722031534411 := by
  unfold tailWord_4433720
  simp only [CollatzResearch.WordTrace]
  refine ⟨80855526748698566967909307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107807368998264755957212409 80855526748698566967909307)
  ·
    refine ⟨121283290123047850451863961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80855526748698566967909307 121283290123047850451863961)
    ·
      refine ⟨90962467592285887838897971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121283290123047850451863961 90962467592285887838897971)
      ·
        refine ⟨136443701388428831758346957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90962467592285887838897971 136443701388428831758346957)
        ·
          refine ⟨51166388020660811909380109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136443701388428831758346957 51166388020660811909380109)
          ·
            refine ⟨19187395507747804466017541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51166388020660811909380109 19187395507747804466017541)
            ·
              refine ⟨3597636657702713337378289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19187395507747804466017541 3597636657702713337378289)
              ·
                refine ⟨2698227493277035003033717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3597636657702713337378289 2698227493277035003033717)
                ·
                  refine ⟨252958827494722031534411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2698227493277035003033717 252958827494722031534411)
                  ·
                    rfl

theorem cell23_4433720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4, 2, 5].length) (baseStart_4433720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4433720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4433720 prefixEnd_4433720 := by exact prefixLift 4433720
  have htrace : WordTrace (prefixWord ++ tailWord_4433720) baseStart_4433720 baseEnd_4433720 := by
    simpa [prefixWord, tailWord_4433720, baseEnd_4433720] using wordTrace_append hprefix tailTrace_4433720
  have hstable : (prefixWord ++ tailWord_4433720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4433720).length < 2 ^ (prefixWord ++ tailWord_4433720).sum := by decide
  have hdescent : baseEnd_4433720 < baseStart_4433720 := by decide
  rcases family_descends (prefixWord ++ tailWord_4433720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4433753 : List Nat := [1, 2, 1, 2, 2, 3, 1, 2, 1, 6, 2]
def baseStart_4433753 : Nat := 118140960795 + 4433753 * 2 ^ 59
def prefixEnd_4433753 : Nat := 4983230072969 + 3 ^ 40 * 4433753 * 2
def baseEnd_4433753 : Nat := 2276646392314096654697047

theorem tailTrace_4433753 : CollatzResearch.WordTrace tailWord_4433753 prefixEnd_4433753 2276646392314096654697047 := by
  unfold tailWord_4433753
  simp only [CollatzResearch.WordTrace]
  refine ⟨161712257106277580571769913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107808171404185053714513275 161712257106277580571769913)
  ·
    refine ⟨121284192829708185428827435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161712257106277580571769913 121284192829708185428827435)
    ·
      refine ⟨181926289244562278143241153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121284192829708185428827435 181926289244562278143241153)
      ·
        refine ⟨136444716933421708607430865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181926289244562278143241153 136444716933421708607430865)
        ·
          refine ⟨102333537700066281455573149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136444716933421708607430865 102333537700066281455573149)
          ·
            refine ⟨38375076637524855545839931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102333537700066281455573149 38375076637524855545839931)
            ·
              refine ⟨57562614956287283318759897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38375076637524855545839931 57562614956287283318759897)
              ·
                refine ⟨43171961217215462489069923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57562614956287283318759897 43171961217215462489069923)
                ·
                  refine ⟨64757941825823193733604885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43171961217215462489069923 64757941825823193733604885)
                  ·
                    refine ⟨3035528523085462206262729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 64757941825823193733604885 3035528523085462206262729)
                    ·
                      refine ⟨2276646392314096654697047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3035528523085462206262729 2276646392314096654697047)
                      ·
                        rfl

theorem cell23_4433753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 6, 2].length) (baseStart_4433753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4433753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4433753 prefixEnd_4433753 := by exact prefixLift 4433753
  have htrace : WordTrace (prefixWord ++ tailWord_4433753) baseStart_4433753 baseEnd_4433753 := by
    simpa [prefixWord, tailWord_4433753, baseEnd_4433753] using wordTrace_append hprefix tailTrace_4433753
  have hstable : (prefixWord ++ tailWord_4433753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4433753).length < 2 ^ (prefixWord ++ tailWord_4433753).sum := by decide
  have hdescent : baseEnd_4433753 < baseStart_4433753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4433753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4433836 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 2, 10]
def baseStart_4433836 : Nat := 118140960795 + 4433836 * 2 ^ 59
def prefixEnd_4433836 : Nat := 4983230072969 + 3 ^ 40 * 4433836 * 2
def baseEnd_4433836 : Nat := 758896337069473276653055

theorem tailTrace_4433836 : CollatzResearch.WordTrace tailWord_4433836 prefixEnd_4433836 758896337069473276653055 := by
  unfold tailWord_4433836
  simp only [CollatzResearch.WordTrace]
  refine ⟨80857642182488442873520681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107810189576651257164694241 80857642182488442873520681)
  ·
    refine ⟨60643231636866332155140511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80857642182488442873520681 60643231636866332155140511)
    ·
      refine ⟨90964847455299498232710767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60643231636866332155140511 90964847455299498232710767)
      ·
        refine ⟨136447271182949247349066151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90964847455299498232710767 136447271182949247349066151)
        ·
          refine ⟨204670906774423871023599227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136447271182949247349066151 204670906774423871023599227)
          ·
            refine ⟨307006360161635806535398841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204670906774423871023599227 307006360161635806535398841)
            ·
              refine ⟨230254770121226854901549131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 307006360161635806535398841 230254770121226854901549131)
              ·
                refine ⟨345382155181840282352323697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 230254770121226854901549131 345382155181840282352323697)
                ·
                  refine ⟨259036616386380211764242773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 345382155181840282352323697 259036616386380211764242773)
                  ·
                    refine ⟨758896337069473276653055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 259036616386380211764242773 758896337069473276653055)
                    ·
                      rfl

theorem cell23_4433836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 10].length) (baseStart_4433836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4433836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4433836 prefixEnd_4433836 := by exact prefixLift 4433836
  have htrace : WordTrace (prefixWord ++ tailWord_4433836) baseStart_4433836 baseEnd_4433836 := by
    simpa [prefixWord, tailWord_4433836, baseEnd_4433836] using wordTrace_append hprefix tailTrace_4433836
  have hstable : (prefixWord ++ tailWord_4433836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4433836).length < 2 ^ (prefixWord ++ tailWord_4433836).sum := by decide
  have hdescent : baseEnd_4433836 < baseStart_4433836 := by decide
  rcases family_descends (prefixWord ++ tailWord_4433836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4433843 : List Nat := [1, 1, 1, 2, 3, 1, 4, 2, 3, 1, 4]
def baseStart_4433843 : Nat := 118140960795 + 4433843 * 2 ^ 59
def prefixEnd_4433843 : Nat := 4983230072969 + 3 ^ 40 * 4433843 * 2
def baseEnd_4433843 : Nat := 2276692605573001302571633

theorem tailTrace_4433843 : CollatzResearch.WordTrace tailWord_4433843 prefixEnd_4433843 2276692605573001302571633 := by
  unfold tailWord_4433843
  simp only [CollatzResearch.WordTrace]
  refine ⟨161715539675951525942546183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107810359783967683961697455 161715539675951525942546183)
  ·
    refine ⟨242573309513927288913819275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161715539675951525942546183 242573309513927288913819275)
    ·
      refine ⟨363859964270890933370728913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242573309513927288913819275 363859964270890933370728913)
      ·
        refine ⟨272894973203168200028046685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 363859964270890933370728913 272894973203168200028046685)
        ·
          refine ⟨102335614951188075010517507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 272894973203168200028046685 102335614951188075010517507)
          ·
            refine ⟨153503422426782112515776261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102335614951188075010517507 153503422426782112515776261)
            ·
              refine ⟨28781891705021646096708049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 153503422426782112515776261 28781891705021646096708049)
              ·
                refine ⟨21586418778766234572531037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28781891705021646096708049 21586418778766234572531037)
                ·
                  refine ⟨8094907042037337964699139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21586418778766234572531037 8094907042037337964699139)
                  ·
                    refine ⟨12142360563056006947048709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8094907042037337964699139 12142360563056006947048709)
                    ·
                      refine ⟨2276692605573001302571633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12142360563056006947048709 2276692605573001302571633)
                      ·
                        rfl

theorem cell23_4433843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 3, 1, 4].length) (baseStart_4433843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4433843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4433843 prefixEnd_4433843 := by exact prefixLift 4433843
  have htrace : WordTrace (prefixWord ++ tailWord_4433843) baseStart_4433843 baseEnd_4433843 := by
    simpa [prefixWord, tailWord_4433843, baseEnd_4433843] using wordTrace_append hprefix tailTrace_4433843
  have hstable : (prefixWord ++ tailWord_4433843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4433843).length < 2 ^ (prefixWord ++ tailWord_4433843).sum := by decide
  have hdescent : baseEnd_4433843 < baseStart_4433843 := by decide
  rcases family_descends (prefixWord ++ tailWord_4433843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4433874 : List Nat := [3, 2, 2, 3, 2, 1, 3, 1, 1, 5]
def baseStart_4433874 : Nat := 118140960795 + 4433874 * 2 ^ 59
def prefixEnd_4433874 : Nat := 4983230072969 + 3 ^ 40 * 4433874 * 2
def baseEnd_4433874 : Nat := 758902841157763560427997

theorem tailTrace_4433874 : CollatzResearch.WordTrace tailWord_4433874 prefixEnd_4433874 758902841157763560427997 := by
  unfold tailWord_4433874
  simp only [CollatzResearch.WordTrace]
  refine ⟨40429167584709804559231169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107811113559226145491283117 40429167584709804559231169)
  ·
    refine ⟨30321875688532353419423377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40429167584709804559231169 30321875688532353419423377)
    ·
      refine ⟨22741406766399265064567533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30321875688532353419423377 22741406766399265064567533)
      ·
        refine ⟨8528027537399724399212825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22741406766399265064567533 8528027537399724399212825)
        ·
          refine ⟨6396020653049793299409619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8528027537399724399212825 6396020653049793299409619)
          ·
            refine ⟨9594030979574689949114429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6396020653049793299409619 9594030979574689949114429)
            ·
              refine ⟨3597761617340508730917911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9594030979574689949114429 3597761617340508730917911)
              ·
                refine ⟨5396642426010763096376867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3597761617340508730917911 5396642426010763096376867)
                ·
                  refine ⟨8094963639016144644565301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5396642426010763096376867 8094963639016144644565301)
                  ·
                    refine ⟨758902841157763560427997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8094963639016144644565301 758902841157763560427997)
                    ·
                      rfl

theorem cell23_4433874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3, 1, 1, 5].length) (baseStart_4433874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4433874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4433874 prefixEnd_4433874 := by exact prefixLift 4433874
  have htrace : WordTrace (prefixWord ++ tailWord_4433874) baseStart_4433874 baseEnd_4433874 := by
    simpa [prefixWord, tailWord_4433874, baseEnd_4433874] using wordTrace_append hprefix tailTrace_4433874
  have hstable : (prefixWord ++ tailWord_4433874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4433874).length < 2 ^ (prefixWord ++ tailWord_4433874).sum := by decide
  have hdescent : baseEnd_4433874 < baseStart_4433874 := by decide
  rcases family_descends (prefixWord ++ tailWord_4433874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4433887 : List Nat := [1, 1, 2, 3, 4, 2, 2, 2, 2, 4]
def baseStart_4433887 : Nat := 118140960795 + 4433887 * 2 ^ 59
def prefixEnd_4433887 : Nat := 4983230072969 + 3 ^ 40 * 4433887 * 2
def baseEnd_4433887 : Nat := 758905066240599710140477

theorem tailTrace_4433887 : CollatzResearch.WordTrace tailWord_4433887 prefixEnd_4433887 758905066240599710140477 := by
  unfold tailWord_4433887
  simp only [CollatzResearch.WordTrace]
  refine ⟨161717144487792121457147915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107811429658528080971431943 161717144487792121457147915)
  ·
    refine ⟨242575716731688182185721873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161717144487792121457147915 242575716731688182185721873)
    ·
      refine ⟨181931787548766136639291405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 242575716731688182185721873 181931787548766136639291405)
      ·
        refine ⟨68224420330787301239734277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 181931787548766136639291405 68224420330787301239734277)
        ·
          refine ⟨12792078812022618982450177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68224420330787301239734277 12792078812022618982450177)
          ·
            refine ⟨9594059109016964236837633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12792078812022618982450177 9594059109016964236837633)
            ·
              refine ⟨7195544331762723177628225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9594059109016964236837633 7195544331762723177628225)
              ·
                refine ⟨5396658248822042383221169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7195544331762723177628225 5396658248822042383221169)
                ·
                  refine ⟨4047493686616531787415877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5396658248822042383221169 4047493686616531787415877)
                  ·
                    refine ⟨758905066240599710140477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4047493686616531787415877 758905066240599710140477)
                    ·
                      rfl

theorem cell23_4433887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 2, 2, 4].length) (baseStart_4433887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4433887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4433887 prefixEnd_4433887 := by exact prefixLift 4433887
  have htrace : WordTrace (prefixWord ++ tailWord_4433887) baseStart_4433887 baseEnd_4433887 := by
    simpa [prefixWord, tailWord_4433887, baseEnd_4433887] using wordTrace_append hprefix tailTrace_4433887
  have hstable : (prefixWord ++ tailWord_4433887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4433887).length < 2 ^ (prefixWord ++ tailWord_4433887).sum := by decide
  have hdescent : baseEnd_4433887 < baseStart_4433887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4433887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4433963 : List Nat := [1, 1, 1, 1, 2, 1, 4, 3, 1, 4, 4]
def baseStart_4433963 : Nat := 118140960795 + 4433963 * 2 ^ 59
def prefixEnd_4433963 : Nat := 4983230072969 + 3 ^ 40 * 4433963 * 2
def baseEnd_4433963 : Nat := 2276754223251540833071081

theorem tailTrace_4433963 : CollatzResearch.WordTrace tailWord_4433963 prefixEnd_4433963 2276754223251540833071081 := by
  unfold tailWord_4433963
  simp only [CollatzResearch.WordTrace]
  refine ⟨161719916435516786436914543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107813277623677857624609695 161719916435516786436914543)
  ·
    refine ⟨242579874653275179655371815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161719916435516786436914543 242579874653275179655371815)
    ·
      refine ⟨363869811979912769483057723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242579874653275179655371815 363869811979912769483057723)
      ·
        refine ⟨545804717969869154224586585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 363869811979912769483057723 545804717969869154224586585)
        ·
          refine ⟨409353538477401865668439939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 545804717969869154224586585 409353538477401865668439939)
          ·
            refine ⟨614030307716102798502659909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 409353538477401865668439939 614030307716102798502659909)
            ·
              refine ⟨115130682696769274719248733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 614030307716102798502659909 115130682696769274719248733)
              ·
                refine ⟨43174006011288478019718275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 115130682696769274719248733 43174006011288478019718275)
                ·
                  refine ⟨64761009016932717029577413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43174006011288478019718275 64761009016932717029577413)
                  ·
                    refine ⟨12142689190674884443045765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 64761009016932717029577413 12142689190674884443045765)
                    ·
                      refine ⟨2276754223251540833071081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12142689190674884443045765 2276754223251540833071081)
                      ·
                        rfl

theorem cell23_4433963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 4, 4].length) (baseStart_4433963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4433963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4433963 prefixEnd_4433963 := by exact prefixLift 4433963
  have htrace : WordTrace (prefixWord ++ tailWord_4433963) baseStart_4433963 baseEnd_4433963 := by
    simpa [prefixWord, tailWord_4433963, baseEnd_4433963] using wordTrace_append hprefix tailTrace_4433963
  have hstable : (prefixWord ++ tailWord_4433963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4433963).length < 2 ^ (prefixWord ++ tailWord_4433963).sum := by decide
  have hdescent : baseEnd_4433963 < baseStart_4433963 := by decide
  rcases family_descends (prefixWord ++ tailWord_4433963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4434018 : List Nat := [3, 3, 2, 2, 2, 1, 1, 3, 2, 2, 2]
def baseStart_4434018 : Nat := 118140960795 + 4434018 * 2 ^ 59
def prefixEnd_4434018 : Nat := 4983230072969 + 3 ^ 40 * 4434018 * 2
def baseEnd_4434018 : Nat := 2276782464687538117883329

theorem tailTrace_4434018 : CollatzResearch.WordTrace tailWord_4434018 prefixEnd_4434018 2276782464687538117883329 := by
  unfold tailWord_4434018
  simp only [CollatzResearch.WordTrace]
  refine ⟨40430480612579382707541677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107814614966878353886777805 40430480612579382707541677)
  ·
    refine ⟨15161430229717268515328129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40430480612579382707541677 15161430229717268515328129)
    ·
      refine ⟨11371072672287951386496097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15161430229717268515328129 11371072672287951386496097)
      ·
        refine ⟨8528304504215963539872073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11371072672287951386496097 8528304504215963539872073)
        ·
          refine ⟨6396228378161972654904055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8528304504215963539872073 6396228378161972654904055)
          ·
            refine ⟨9594342567242958982356083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6396228378161972654904055 9594342567242958982356083)
            ·
              refine ⟨14391513850864438473534125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9594342567242958982356083 14391513850864438473534125)
              ·
                refine ⟨5396817694074164427575297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14391513850864438473534125 5396817694074164427575297)
                ·
                  refine ⟨4047613270555623320681473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5396817694074164427575297 4047613270555623320681473)
                  ·
                    refine ⟨3035709952916717490511105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4047613270555623320681473 3035709952916717490511105)
                    ·
                      refine ⟨2276782464687538117883329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3035709952916717490511105 2276782464687538117883329)
                      ·
                        rfl

theorem cell23_4434018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_4434018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4434018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4434018 prefixEnd_4434018 := by exact prefixLift 4434018
  have htrace : WordTrace (prefixWord ++ tailWord_4434018) baseStart_4434018 baseEnd_4434018 := by
    simpa [prefixWord, tailWord_4434018, baseEnd_4434018] using wordTrace_append hprefix tailTrace_4434018
  have hstable : (prefixWord ++ tailWord_4434018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4434018).length < 2 ^ (prefixWord ++ tailWord_4434018).sum := by decide
  have hdescent : baseEnd_4434018 < baseStart_4434018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4434018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4434030 : List Nat := [4, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7]
def baseStart_4434030 : Nat := 118140960795 + 4434030 * 2 ^ 59
def prefixEnd_4434030 : Nat := 4983230072969 + 3 ^ 40 * 4434030 * 2
def baseEnd_4434030 : Nat := 2276788626455392070933273

theorem tailTrace_4434030 : CollatzResearch.WordTrace tailWord_4434030 prefixEnd_4434030 2276788626455392070933273 := by
  unfold tailWord_4434030
  simp only [CollatzResearch.WordTrace]
  refine ⟨20215295015784257109950443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107814906750849371253069029 20215295015784257109950443)
  ·
    refine ⟨30322942523676385664925665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20215295015784257109950443 30322942523676385664925665)
    ·
      refine ⟨22742206892757289248694249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30322942523676385664925665 22742206892757289248694249)
      ·
        refine ⟨17056655169567966936520687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22742206892757289248694249 17056655169567966936520687)
        ·
          refine ⟨25584982754351950404781031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17056655169567966936520687 25584982754351950404781031)
          ·
            refine ⟨38377474131527925607171547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25584982754351950404781031 38377474131527925607171547)
            ·
              refine ⟨57566211197291888410757321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38377474131527925607171547 57566211197291888410757321)
              ·
                refine ⟨43174658397968916308067991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57566211197291888410757321 43174658397968916308067991)
                ·
                  refine ⟨64761987596953374462101987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43174658397968916308067991 64761987596953374462101987)
                  ·
                    refine ⟨97142981395430061693152981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 64761987596953374462101987 97142981395430061693152981)
                    ·
                      refine ⟨2276788626455392070933273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 97142981395430061693152981 2276788626455392070933273)
                      ·
                        rfl

theorem cell23_4434030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_4434030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4434030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4434030 prefixEnd_4434030 := by exact prefixLift 4434030
  have htrace : WordTrace (prefixWord ++ tailWord_4434030) baseStart_4434030 baseEnd_4434030 := by
    simpa [prefixWord, tailWord_4434030, baseEnd_4434030] using wordTrace_append hprefix tailTrace_4434030
  have hstable : (prefixWord ++ tailWord_4434030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4434030).length < 2 ^ (prefixWord ++ tailWord_4434030).sum := by decide
  have hdescent : baseEnd_4434030 < baseStart_4434030 := by decide
  rcases family_descends (prefixWord ++ tailWord_4434030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4434043 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 9]
def baseStart_4434043 : Nat := 118140960795 + 4434043 * 2 ^ 59
def prefixEnd_4434043 : Nat := 4983230072969 + 3 ^ 40 * 4434043 * 2
def baseEnd_4434043 : Nat := 2276795301703900520070713

theorem tailTrace_4434043 : CollatzResearch.WordTrace tailWord_4434043 prefixEnd_4434043 2276795301703900520070713 := by
  unfold tailWord_4434043
  simp only [CollatzResearch.WordTrace]
  refine ⟨161722834275226960099826783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107815222850151306733217855 161722834275226960099826783)
  ·
    refine ⟨242584251412840440149740175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161722834275226960099826783 242584251412840440149740175)
    ·
      refine ⟨363876377119260660224610263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242584251412840440149740175 363876377119260660224610263)
      ·
        refine ⟨545814565678890990336915395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 363876377119260660224610263 545814565678890990336915395)
        ·
          refine ⟨818721848518336485505373093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 545814565678890990336915395 818721848518336485505373093)
          ·
            refine ⟨153510346597188091032257455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 818721848518336485505373093 153510346597188091032257455)
            ·
              refine ⟨230265519895782136548386183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153510346597188091032257455 230265519895782136548386183)
              ·
                refine ⟨345398279843673204822579275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 230265519895782136548386183 345398279843673204822579275)
                ·
                  refine ⟨518097419765509807233868913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 345398279843673204822579275 518097419765509807233868913)
                  ·
                    refine ⟨388573064824132355425401685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 518097419765509807233868913 388573064824132355425401685)
                    ·
                      refine ⟨2276795301703900520070713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 388573064824132355425401685 2276795301703900520070713)
                      ·
                        rfl

theorem cell23_4434043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 9].length) (baseStart_4434043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4434043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4434043 prefixEnd_4434043 := by exact prefixLift 4434043
  have htrace : WordTrace (prefixWord ++ tailWord_4434043) baseStart_4434043 baseEnd_4434043 := by
    simpa [prefixWord, tailWord_4434043, baseEnd_4434043] using wordTrace_append hprefix tailTrace_4434043
  have hstable : (prefixWord ++ tailWord_4434043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4434043).length < 2 ^ (prefixWord ++ tailWord_4434043).sum := by decide
  have hdescent : baseEnd_4434043 < baseStart_4434043 := by decide
  rcases family_descends (prefixWord ++ tailWord_4434043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4434057 : List Nat := [1, 2, 1, 1, 4, 2, 2, 2, 2, 4, 2]
def baseStart_4434057 : Nat := 118140960795 + 4434057 * 2 ^ 59
def prefixEnd_4434057 : Nat := 4983230072969 + 3 ^ 40 * 4434057 * 2
def baseEnd_4434057 : Nat := 2276802490433063465295649

theorem tailTrace_4434057 : CollatzResearch.WordTrace tailWord_4434057 prefixEnd_4434057 2276802490433063465295649 := by
  unfold tailWord_4434057
  simp only [CollatzResearch.WordTrace]
  refine ⟨161723344897176240490836425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107815563264784160327224283 161723344897176240490836425)
  ·
    refine ⟨121292508672882180368127319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161723344897176240490836425 121292508672882180368127319)
    ·
      refine ⟨181938763009323270552190979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121292508672882180368127319 181938763009323270552190979)
      ·
        refine ⟨272908144513984905828286469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181938763009323270552190979 272908144513984905828286469)
        ·
          refine ⟨51170277096372169842803713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 272908144513984905828286469 51170277096372169842803713)
          ·
            refine ⟨38377707822279127382102785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51170277096372169842803713 38377707822279127382102785)
            ·
              refine ⟨28783280866709345536577089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38377707822279127382102785 28783280866709345536577089)
              ·
                refine ⟨21587460650032009152432817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28783280866709345536577089 21587460650032009152432817)
                ·
                  refine ⟨16190595487524006864324613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21587460650032009152432817 16190595487524006864324613)
                  ·
                    refine ⟨3035736653910751287060865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16190595487524006864324613 3035736653910751287060865)
                    ·
                      refine ⟨2276802490433063465295649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3035736653910751287060865 2276802490433063465295649)
                      ·
                        rfl

theorem cell23_4434057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 2, 4, 2].length) (baseStart_4434057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4434057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4434057 prefixEnd_4434057 := by exact prefixLift 4434057
  have htrace : WordTrace (prefixWord ++ tailWord_4434057) baseStart_4434057 baseEnd_4434057 := by
    simpa [prefixWord, tailWord_4434057, baseEnd_4434057] using wordTrace_append hprefix tailTrace_4434057
  have hstable : (prefixWord ++ tailWord_4434057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4434057).length < 2 ^ (prefixWord ++ tailWord_4434057).sum := by decide
  have hdescent : baseEnd_4434057 < baseStart_4434057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4434057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4434060 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 5, 4, 3]
def baseStart_4434060 : Nat := 118140960795 + 4434060 * 2 ^ 59
def prefixEnd_4434060 : Nat := 4983230072969 + 3 ^ 40 * 4434060 * 2
def baseEnd_4434060 : Nat := 2276804030875026953558135

theorem tailTrace_4434060 : CollatzResearch.WordTrace tailWord_4434060 prefixEnd_4434060 2276804030875026953558135 := by
  unfold tailWord_4434060
  simp only [CollatzResearch.WordTrace]
  refine ⟨80861727158082686001597817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107815636210776914668797089 80861727158082686001597817)
  ·
    refine ⟨60646295368562014501198363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80861727158082686001597817 60646295368562014501198363)
    ·
      refine ⟨90969443052843021751797545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60646295368562014501198363 90969443052843021751797545)
      ·
        refine ⟨68227082289632266313848159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90969443052843021751797545 68227082289632266313848159)
        ·
          refine ⟨102340623434448399470772239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68227082289632266313848159 102340623434448399470772239)
          ·
            refine ⟨153510935151672599206158359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102340623434448399470772239 153510935151672599206158359)
            ·
              refine ⟨230266402727508898809237539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153510935151672599206158359 230266402727508898809237539)
              ·
                refine ⟨345399604091263348213856309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 230266402727508898809237539 345399604091263348213856309)
                ·
                  refine ⟨32381212883555938895049029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 345399604091263348213856309 32381212883555938895049029)
                  ·
                    refine ⟨6071477415666738542821693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32381212883555938895049029 6071477415666738542821693)
                    ·
                      refine ⟨2276804030875026953558135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6071477415666738542821693 2276804030875026953558135)
                      ·
                        rfl

theorem cell23_4434060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 5, 4, 3].length) (baseStart_4434060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4434060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4434060 prefixEnd_4434060 := by exact prefixLift 4434060
  have htrace : WordTrace (prefixWord ++ tailWord_4434060) baseStart_4434060 baseEnd_4434060 := by
    simpa [prefixWord, tailWord_4434060, baseEnd_4434060] using wordTrace_append hprefix tailTrace_4434060
  have hstable : (prefixWord ++ tailWord_4434060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4434060).length < 2 ^ (prefixWord ++ tailWord_4434060).sum := by decide
  have hdescent : baseEnd_4434060 < baseStart_4434060 := by decide
  rcases family_descends (prefixWord ++ tailWord_4434060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4434084 : List Nat := [2, 3, 1, 2, 4, 1, 1, 2, 3, 4]
def baseStart_4434084 : Nat := 118140960795 + 4434084 * 2 ^ 59
def prefixEnd_4434084 : Nat := 4983230072969 + 3 ^ 40 * 4434084 * 2
def baseEnd_4434084 : Nat := 758938784803578286552675

theorem tailTrace_4434084 : CollatzResearch.WordTrace tailWord_4434084 prefixEnd_4434084 758938784803578286552675 := by
  unfold tailWord_4434084
  simp only [CollatzResearch.WordTrace]
  refine ⟨80862164834039212051034653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107816219778718949401379537 80862164834039212051034653)
  ·
    refine ⟨30323311812764704519137995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80862164834039212051034653 30323311812764704519137995)
    ·
      refine ⟨45484967719147056778706993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30323311812764704519137995 45484967719147056778706993)
      ·
        refine ⟨34113725789360292584030245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45484967719147056778706993 34113725789360292584030245)
        ·
          refine ⟨6396323585505054859505671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34113725789360292584030245 6396323585505054859505671)
          ·
            refine ⟨9594485378257582289258507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6396323585505054859505671 9594485378257582289258507)
            ·
              refine ⟨14391728067386373433887761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9594485378257582289258507 14391728067386373433887761)
              ·
                refine ⟨10793796050539780075415821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14391728067386373433887761 10793796050539780075415821)
                ·
                  refine ⟨4047673518952417528280933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10793796050539780075415821 4047673518952417528280933)
                  ·
                    refine ⟨758938784803578286552675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4047673518952417528280933 758938784803578286552675)
                    ·
                      rfl

theorem cell23_4434084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 2, 3, 4].length) (baseStart_4434084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4434084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4434084 prefixEnd_4434084 := by exact prefixLift 4434084
  have htrace : WordTrace (prefixWord ++ tailWord_4434084) baseStart_4434084 baseEnd_4434084 := by
    simpa [prefixWord, tailWord_4434084, baseEnd_4434084] using wordTrace_append hprefix tailTrace_4434084
  have hstable : (prefixWord ++ tailWord_4434084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4434084).length < 2 ^ (prefixWord ++ tailWord_4434084).sum := by decide
  have hdescent : baseEnd_4434084 < baseStart_4434084 := by decide
  rcases family_descends (prefixWord ++ tailWord_4434084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4434107 : List Nat := [1, 1, 1, 1, 1, 2, 5, 2, 5, 1, 3]
def baseStart_4434107 : Nat := 118140960795 + 4434107 * 2 ^ 59
def prefixEnd_4434107 : Nat := 4983230072969 + 3 ^ 40 * 4434107 * 2
def baseEnd_4434107 : Nat := 2276828164465788269670419

theorem tailTrace_4434107 : CollatzResearch.WordTrace tailWord_4434107 prefixEnd_4434107 2276828164465788269670419 := by
  unfold tailWord_4434107
  simp only [CollatzResearch.WordTrace]
  refine ⟨161725168546995099030156575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107816779031330066020104383 161725168546995099030156575)
  ·
    refine ⟨242587752820492648545234863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161725168546995099030156575 242587752820492648545234863)
    ·
      refine ⟨363881629230738972817852295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242587752820492648545234863 363881629230738972817852295)
      ·
        refine ⟨545822443846108459226778443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 363881629230738972817852295 545822443846108459226778443)
        ·
          refine ⟨818733665769162688840167665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 545822443846108459226778443 818733665769162688840167665)
          ·
            refine ⟨614050249326872016630125749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 818733665769162688840167665 614050249326872016630125749)
            ·
              refine ⟨57567210874394251559074289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 614050249326872016630125749 57567210874394251559074289)
              ·
                refine ⟨43175408155795688669305717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57567210874394251559074289 43175408155795688669305717)
                ·
                  refine ⟨4047694514605845812747411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43175408155795688669305717 4047694514605845812747411)
                  ·
                    refine ⟨6071541771908768719121117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4047694514605845812747411 6071541771908768719121117)
                    ·
                      refine ⟨2276828164465788269670419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6071541771908768719121117 2276828164465788269670419)
                      ·
                        rfl

theorem cell23_4434107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 5, 1, 3].length) (baseStart_4434107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4434107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4434107 prefixEnd_4434107 := by exact prefixLift 4434107
  have htrace : WordTrace (prefixWord ++ tailWord_4434107) baseStart_4434107 baseEnd_4434107 := by
    simpa [prefixWord, tailWord_4434107, baseEnd_4434107] using wordTrace_append hprefix tailTrace_4434107
  have hstable : (prefixWord ++ tailWord_4434107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4434107).length < 2 ^ (prefixWord ++ tailWord_4434107).sum := by decide
  have hdescent : baseEnd_4434107 < baseStart_4434107 := by decide
  rcases family_descends (prefixWord ++ tailWord_4434107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4434141 : List Nat := [1, 4, 3, 2, 1, 1, 2, 2, 3, 1, 3]
def baseStart_4434141 : Nat := 118140960795 + 4434141 * 2 ^ 59
def prefixEnd_4434141 : Nat := 4983230072969 + 3 ^ 40 * 4434141 * 2
def baseEnd_4434141 : Nat := 2276845622808041136645263

theorem tailTrace_4434141 : CollatzResearch.WordTrace tailWord_4434141 prefixEnd_4434141 2276845622808041136645263 := by
  unfold tailWord_4434141
  simp only [CollatzResearch.WordTrace]
  refine ⟨161726408628871922836894277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107817605752581281891262851 161726408628871922836894277)
  ·
    refine ⟨30323701617913485531917677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 161726408628871922836894277 30323701617913485531917677)
    ·
      refine ⟨11371388106717557074469129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30323701617913485531917677 11371388106717557074469129)
      ·
        refine ⟨8528541080038167805851847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11371388106717557074469129 8528541080038167805851847)
        ·
          refine ⟨12792811620057251708777771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8528541080038167805851847 12792811620057251708777771)
          ·
            refine ⟨19189217430085877563166657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12792811620057251708777771 19189217430085877563166657)
            ·
              refine ⟨14391913072564408172374993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19189217430085877563166657 14391913072564408172374993)
              ·
                refine ⟨10793934804423306129281245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14391913072564408172374993 10793934804423306129281245)
                ·
                  refine ⟨4047725551658739798480467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10793934804423306129281245 4047725551658739798480467)
                  ·
                    refine ⟨6071588327488109697720701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4047725551658739798480467 6071588327488109697720701)
                    ·
                      refine ⟨2276845622808041136645263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6071588327488109697720701 2276845622808041136645263)
                      ·
                        rfl

theorem cell23_4434141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_4434141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4434141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4434141 prefixEnd_4434141 := by exact prefixLift 4434141
  have htrace : WordTrace (prefixWord ++ tailWord_4434141) baseStart_4434141 baseEnd_4434141 := by
    simpa [prefixWord, tailWord_4434141, baseEnd_4434141] using wordTrace_append hprefix tailTrace_4434141
  have hstable : (prefixWord ++ tailWord_4434141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4434141).length < 2 ^ (prefixWord ++ tailWord_4434141).sum := by decide
  have hdescent : baseEnd_4434141 < baseStart_4434141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4434141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4434170 : List Nat := [3, 1, 1, 1, 1, 5, 11]
def baseStart_4434170 : Nat := 118140960795 + 4434170 * 2 ^ 59
def prefixEnd_4434170 : Nat := 4983230072969 + 3 ^ 40 * 4434170 * 2
def baseEnd_4434170 : Nat := 28109389058605203989909

theorem tailTrace_4434170 : CollatzResearch.WordTrace tailWord_4434170 prefixEnd_4434170 28109389058605203989909 := by
  unfold tailWord_4434170
  simp only [CollatzResearch.WordTrace]
  refine ⟨40431866586441715197424991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107818310897177907193133309 40431866586441715197424991)
  ·
    refine ⟨60647799879662572796137487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40431866586441715197424991 60647799879662572796137487)
    ·
      refine ⟨90971699819493859194206231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60647799879662572796137487 90971699819493859194206231)
      ·
        refine ⟨136457549729240788791309347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90971699819493859194206231 136457549729240788791309347)
        ·
          refine ⟨204686324593861183186964021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136457549729240788791309347 204686324593861183186964021)
          ·
            refine ⟨19189342930674485923777877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 204686324593861183186964021 19189342930674485923777877)
            ·
              refine ⟨28109389058605203989909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 19189342930674485923777877 28109389058605203989909)
              ·
                rfl

theorem cell23_4434170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 11].length) (baseStart_4434170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4434170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4434170 prefixEnd_4434170 := by exact prefixLift 4434170
  have htrace : WordTrace (prefixWord ++ tailWord_4434170) baseStart_4434170 baseEnd_4434170 := by
    simpa [prefixWord, tailWord_4434170, baseEnd_4434170] using wordTrace_append hprefix tailTrace_4434170
  have hstable : (prefixWord ++ tailWord_4434170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4434170).length < 2 ^ (prefixWord ++ tailWord_4434170).sum := by decide
  have hdescent : baseEnd_4434170 < baseStart_4434170 := by decide
  rcases family_descends (prefixWord ++ tailWord_4434170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4434174 : List Nat := [4, 2, 2, 1, 1, 1, 1, 3, 4, 4]
def baseStart_4434174 : Nat := 118140960795 + 4434174 * 2 ^ 59
def prefixEnd_4434174 : Nat := 4983230072969 + 3 ^ 40 * 4434174 * 2
def baseEnd_4434174 : Nat := 758954189223213169177537

theorem tailTrace_4434174 : CollatzResearch.WordTrace tailWord_4434174 prefixEnd_4434174 758954189223213169177537 := by
  unfold tailWord_4434174
  simp only [CollatzResearch.WordTrace]
  refine ⟨20215951529719046184105697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107818408158501579648563717 20215951529719046184105697)
  ·
    refine ⟨15161963647289284638079273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20215951529719046184105697 15161963647289284638079273)
    ·
      refine ⟨11371472735466963478559455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15161963647289284638079273 11371472735466963478559455)
      ·
        refine ⟨17057209103200445217839183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11371472735466963478559455 17057209103200445217839183)
        ·
          refine ⟨25585813654800667826758775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17057209103200445217839183 25585813654800667826758775)
          ·
            refine ⟨38378720482201001740138163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25585813654800667826758775 38378720482201001740138163)
            ·
              refine ⟨57568080723301502610207245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38378720482201001740138163 57568080723301502610207245)
              ·
                refine ⟨21588030271238063478827717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57568080723301502610207245 21588030271238063478827717)
                ·
                  refine ⟨4047755675857136902280197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21588030271238063478827717 4047755675857136902280197)
                  ·
                    refine ⟨758954189223213169177537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4047755675857136902280197 758954189223213169177537)
                    ·
                      rfl

theorem cell23_4434174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_4434174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4434174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4434174 prefixEnd_4434174 := by exact prefixLift 4434174
  have htrace : WordTrace (prefixWord ++ tailWord_4434174) baseStart_4434174 baseEnd_4434174 := by
    simpa [prefixWord, tailWord_4434174, baseEnd_4434174] using wordTrace_append hprefix tailTrace_4434174
  have hstable : (prefixWord ++ tailWord_4434174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4434174).length < 2 ^ (prefixWord ++ tailWord_4434174).sum := by decide
  have hdescent : baseEnd_4434174 < baseStart_4434174 := by decide
  rcases family_descends (prefixWord ++ tailWord_4434174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4434218 : List Nat := [3, 1, 4, 2, 3, 1, 1, 1, 1, 1, 5]
def baseStart_4434218 : Nat := 118140960795 + 4434218 * 2 ^ 59
def prefixEnd_4434218 : Nat := 4983230072969 + 3 ^ 40 * 4434218 * 2
def baseEnd_4434218 : Nat := 2276885160818437335382409

theorem tailTrace_4434218 : CollatzResearch.WordTrace tailWord_4434218 prefixEnd_4434218 2276885160818437335382409 := by
  unfold tailWord_4434218
  simp only [CollatzResearch.WordTrace]
  refine ⟨40432304262398241246861827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107819478033061976658298205 40432304262398241246861827)
  ·
    refine ⟨60648456393597361870292741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40432304262398241246861827 60648456393597361870292741)
    ·
      refine ⟨11371585573799505350679889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60648456393597361870292741 11371585573799505350679889)
      ·
        refine ⟨8528689180349629013009917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11371585573799505350679889 8528689180349629013009917)
        ·
          refine ⟨3198258442631110879878719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8528689180349629013009917 3198258442631110879878719)
          ·
            refine ⟨4797387663946666319818079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3198258442631110879878719 4797387663946666319818079)
            ·
              refine ⟨7196081495919999479727119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4797387663946666319818079 7196081495919999479727119)
              ·
                refine ⟨10794122243879999219590679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7196081495919999479727119 10794122243879999219590679)
                ·
                  refine ⟨16191183365819998829386019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10794122243879999219590679 16191183365819998829386019)
                  ·
                    refine ⟨24286775048729998244079029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16191183365819998829386019 24286775048729998244079029)
                    ·
                      refine ⟨2276885160818437335382409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24286775048729998244079029 2276885160818437335382409)
                      ·
                        rfl

theorem cell23_4434218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_4434218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4434218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4434218 prefixEnd_4434218 := by exact prefixLift 4434218
  have htrace : WordTrace (prefixWord ++ tailWord_4434218) baseStart_4434218 baseEnd_4434218 := by
    simpa [prefixWord, tailWord_4434218, baseEnd_4434218] using wordTrace_append hprefix tailTrace_4434218
  have hstable : (prefixWord ++ tailWord_4434218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4434218).length < 2 ^ (prefixWord ++ tailWord_4434218).sum := by decide
  have hdescent : baseEnd_4434218 < baseStart_4434218 := by decide
  rcases family_descends (prefixWord ++ tailWord_4434218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4434247 : List Nat := [1, 1, 4, 1, 2, 2, 3, 1, 2, 6]
def baseStart_4434247 : Nat := 118140960795 + 4434247 * 2 ^ 59
def prefixEnd_4434247 : Nat := 4983230072969 + 3 ^ 40 * 4434247 * 2
def baseEnd_4434247 : Nat := 758966683919139240639925

theorem tailTrace_4434247 : CollatzResearch.WordTrace tailWord_4434247 prefixEnd_4434247 758966683919139240639925 := by
  unfold tailWord_4434247
  simp only [CollatzResearch.WordTrace]
  refine ⟨161730274766487902940252995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107820183177658601960168663 161730274766487902940252995)
  ·
    refine ⟨242595412149731854410379493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161730274766487902940252995 242595412149731854410379493)
    ·
      refine ⟨45486639778074722701946155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 242595412149731854410379493 45486639778074722701946155)
      ·
        refine ⟨68229959667112084052919233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45486639778074722701946155 68229959667112084052919233)
        ·
          refine ⟨51172469750334063039689425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68229959667112084052919233 51172469750334063039689425)
          ·
            refine ⟨38379352312750547279767069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51172469750334063039689425 38379352312750547279767069)
            ·
              refine ⟨14392257117281455229912651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38379352312750547279767069 14392257117281455229912651)
              ·
                refine ⟨21588385675922182844868977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14392257117281455229912651 21588385675922182844868977)
                ·
                  refine ⟨16191289256941637133651733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21588385675922182844868977 16191289256941637133651733)
                  ·
                    refine ⟨758966683919139240639925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16191289256941637133651733 758966683919139240639925)
                    ·
                      rfl

theorem cell23_4434247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 2, 6].length) (baseStart_4434247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4434247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4434247 prefixEnd_4434247 := by exact prefixLift 4434247
  have htrace : WordTrace (prefixWord ++ tailWord_4434247) baseStart_4434247 baseEnd_4434247 := by
    simpa [prefixWord, tailWord_4434247, baseEnd_4434247] using wordTrace_append hprefix tailTrace_4434247
  have hstable : (prefixWord ++ tailWord_4434247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4434247).length < 2 ^ (prefixWord ++ tailWord_4434247).sum := by decide
  have hdescent : baseEnd_4434247 < baseStart_4434247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4434247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4434288 : List Nat := [2, 1, 1, 1, 4, 3, 3, 2, 2, 2, 2]
def baseStart_4434288 : Nat := 118140960795 + 4434288 * 2 ^ 59
def prefixEnd_4434288 : Nat := 4983230072969 + 3 ^ 40 * 4434288 * 2
def baseEnd_4434288 : Nat := 2276921104464252061507087

theorem tailTrace_4434288 : CollatzResearch.WordTrace tailWord_4434288 prefixEnd_4434288 2276921104464252061507087 := by
  unfold tailWord_4434288
  simp only [CollatzResearch.WordTrace]
  refine ⟨80865885079669683471247759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107821180106226244628330345 80865885079669683471247759)
  ·
    refine ⟨121298827619504525206871639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80865885079669683471247759 121298827619504525206871639)
    ·
      refine ⟨181948241429256787810307459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121298827619504525206871639 181948241429256787810307459)
      ·
        refine ⟨272922362143885181715461189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181948241429256787810307459 272922362143885181715461189)
        ·
          refine ⟨51172942901978471571648973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 272922362143885181715461189 51172942901978471571648973)
          ·
            refine ⟨19189853588241926839368365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51172942901978471571648973 19189853588241926839368365)
            ·
              refine ⟨7196195095590722564763137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19189853588241926839368365 7196195095590722564763137)
              ·
                refine ⟨5397146321693041923572353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7196195095590722564763137 5397146321693041923572353)
                ·
                  refine ⟨4047859741269781442679265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5397146321693041923572353 4047859741269781442679265)
                  ·
                    refine ⟨3035894805952336082009449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4047859741269781442679265 3035894805952336082009449)
                    ·
                      refine ⟨2276921104464252061507087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3035894805952336082009449 2276921104464252061507087)
                      ·
                        rfl

theorem cell23_4434288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 2, 2, 2, 2].length) (baseStart_4434288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4434288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4434288 prefixEnd_4434288 := by exact prefixLift 4434288
  have htrace : WordTrace (prefixWord ++ tailWord_4434288) baseStart_4434288 baseEnd_4434288 := by
    simpa [prefixWord, tailWord_4434288, baseEnd_4434288] using wordTrace_append hprefix tailTrace_4434288
  have hstable : (prefixWord ++ tailWord_4434288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4434288).length < 2 ^ (prefixWord ++ tailWord_4434288).sum := by decide
  have hdescent : baseEnd_4434288 < baseStart_4434288 := by decide
  rcases family_descends (prefixWord ++ tailWord_4434288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4434328 : List Nat := [2, 1, 2, 5, 1, 3, 1, 3, 5]
def baseStart_4434328 : Nat := 118140960795 + 4434328 * 2 ^ 59
def prefixEnd_4434328 : Nat := 4983230072969 + 3 ^ 40 * 4434328 * 2
def baseEnd_4434328 : Nat := 252993515965603545000767

theorem tailTrace_4434328 : CollatzResearch.WordTrace tailWord_4434328 prefixEnd_4434328 252993515965603545000767 := by
  unfold tailWord_4434328
  simp only [CollatzResearch.WordTrace]
  refine ⟨80866614539597226886975819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107822152719462969182634425 80866614539597226886975819)
  ·
    refine ⟨121299921809395840330463729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80866614539597226886975819 121299921809395840330463729)
    ·
      refine ⟨90974941357046880247847797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121299921809395840330463729 90974941357046880247847797)
      ·
        refine ⟨8528900752223145023235731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 90974941357046880247847797 8528900752223145023235731)
        ·
          refine ⟨12793351128334717534853597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8528900752223145023235731 12793351128334717534853597)
          ·
            refine ⟨4797506673125519075570099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12793351128334717534853597 4797506673125519075570099)
            ·
              refine ⟨7196260009688278613355149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4797506673125519075570099 7196260009688278613355149)
              ·
                refine ⟨2698597503633104480008181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7196260009688278613355149 2698597503633104480008181)
                ·
                  refine ⟨252993515965603545000767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2698597503633104480008181 252993515965603545000767)
                  ·
                    rfl

theorem cell23_4434328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 3, 5].length) (baseStart_4434328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4434328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4434328 prefixEnd_4434328 := by exact prefixLift 4434328
  have htrace : WordTrace (prefixWord ++ tailWord_4434328) baseStart_4434328 baseEnd_4434328 := by
    simpa [prefixWord, tailWord_4434328, baseEnd_4434328] using wordTrace_append hprefix tailTrace_4434328
  have hstable : (prefixWord ++ tailWord_4434328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4434328).length < 2 ^ (prefixWord ++ tailWord_4434328).sum := by decide
  have hdescent : baseEnd_4434328 < baseStart_4434328 := by decide
  rcases family_descends (prefixWord ++ tailWord_4434328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4434356 : List Nat := [2, 5, 2, 2, 1, 2, 2, 1, 2, 2, 2]
def baseStart_4434356 : Nat := 118140960795 + 4434356 * 2 ^ 59
def prefixEnd_4434356 : Nat := 4983230072969 + 3 ^ 40 * 4434356 * 2
def baseEnd_4434356 : Nat := 2276956021148757795456775

theorem tailTrace_4434356 : CollatzResearch.WordTrace tailWord_4434356 prefixEnd_4434356 2276956021148757795456775 := by
  unfold tailWord_4434356
  simp only [CollatzResearch.WordTrace]
  refine ⟨80867125161546507277985461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107822833548728676370647281 80867125161546507277985461)
  ·
    refine ⟨7581292983894985057311137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 80867125161546507277985461 7581292983894985057311137)
    ·
      refine ⟨5685969737921238792983353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7581292983894985057311137 5685969737921238792983353)
      ·
        refine ⟨4264477303440929094737515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5685969737921238792983353 4264477303440929094737515)
        ·
          refine ⟨6396715955161393642106273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4264477303440929094737515 6396715955161393642106273)
          ·
            refine ⟨4797536966371045231579705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6396715955161393642106273 4797536966371045231579705)
            ·
              refine ⟨3598152724778283923684779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4797536966371045231579705 3598152724778283923684779)
              ·
                refine ⟨5397229087167425885527169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3598152724778283923684779 5397229087167425885527169)
                ·
                  refine ⟨4047921815375569414145377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5397229087167425885527169 4047921815375569414145377)
                  ·
                    refine ⟨3035941361531677060609033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4047921815375569414145377 3035941361531677060609033)
                    ·
                      refine ⟨2276956021148757795456775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3035941361531677060609033 2276956021148757795456775)
                      ·
                        rfl

theorem cell23_4434356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_4434356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4434356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4434356 prefixEnd_4434356 := by exact prefixLift 4434356
  have htrace : WordTrace (prefixWord ++ tailWord_4434356) baseStart_4434356 baseEnd_4434356 := by
    simpa [prefixWord, tailWord_4434356, baseEnd_4434356] using wordTrace_append hprefix tailTrace_4434356
  have hstable : (prefixWord ++ tailWord_4434356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4434356).length < 2 ^ (prefixWord ++ tailWord_4434356).sum := by decide
  have hdescent : baseEnd_4434356 < baseStart_4434356 := by decide
  rcases family_descends (prefixWord ++ tailWord_4434356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4434405 : List Nat := [1, 3, 1, 5, 2, 1, 1, 4, 1, 4]
def baseStart_4434405 : Nat := 118140960795 + 4434405 * 2 ^ 59
def prefixEnd_4434405 : Nat := 4983230072969 + 3 ^ 40 * 4434405 * 2
def baseEnd_4434405 : Nat := 758993727233609367914683

theorem tailTrace_4434405 : CollatzResearch.WordTrace tailWord_4434405 prefixEnd_4434405 758993727233609367914683 := by
  unfold tailWord_4434405
  simp only [CollatzResearch.WordTrace]
  refine ⟨161736037499915495924504669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107824024999943663949669779 161736037499915495924504669)
  ·
    refine ⟨60651014062468310971689251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161736037499915495924504669 60651014062468310971689251)
    ·
      refine ⟨90976521093702466457533877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60651014062468310971689251 90976521093702466457533877)
      ·
        refine ⟨8529048852534606230393801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 90976521093702466457533877 8529048852534606230393801)
        ·
          refine ⟨6396786639400954672795351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8529048852534606230393801 6396786639400954672795351)
          ·
            refine ⟨9595179959101432009193027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6396786639400954672795351 9595179959101432009193027)
            ·
              refine ⟨14392769938652148013789541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9595179959101432009193027 14392769938652148013789541)
              ·
                refine ⟨2698644363497277752585539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14392769938652148013789541 2698644363497277752585539)
                ·
                  refine ⟨4047966545245916628878309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2698644363497277752585539 4047966545245916628878309)
                  ·
                    refine ⟨758993727233609367914683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4047966545245916628878309 758993727233609367914683)
                    ·
                      rfl

theorem cell23_4434405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 4, 1, 4].length) (baseStart_4434405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4434405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4434405 prefixEnd_4434405 := by exact prefixLift 4434405
  have htrace : WordTrace (prefixWord ++ tailWord_4434405) baseStart_4434405 baseEnd_4434405 := by
    simpa [prefixWord, tailWord_4434405, baseEnd_4434405] using wordTrace_append hprefix tailTrace_4434405
  have hstable : (prefixWord ++ tailWord_4434405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4434405).length < 2 ^ (prefixWord ++ tailWord_4434405).sum := by decide
  have hdescent : baseEnd_4434405 < baseStart_4434405 := by decide
  rcases family_descends (prefixWord ++ tailWord_4434405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4434411 : List Nat := [1, 1, 1, 1, 2, 3, 4, 3, 3, 1, 3]
def baseStart_4434411 : Nat := 118140960795 + 4434411 * 2 ^ 59
def prefixEnd_4434411 : Nat := 4983230072969 + 3 ^ 40 * 4434411 * 2
def baseEnd_4434411 : Nat := 2276984262584755080269021

theorem tailTrace_4434411 : CollatzResearch.WordTrace tailWord_4434411 prefixEnd_4434411 2276984262584755080269021 := by
  unfold tailWord_4434411
  simp only [CollatzResearch.WordTrace]
  refine ⟨161736256337893758949223087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107824170891929172632815391 161736256337893758949223087)
  ·
    refine ⟨242604384506840638423834631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161736256337893758949223087 242604384506840638423834631)
    ·
      refine ⟨363906576760260957635751947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242604384506840638423834631 363906576760260957635751947)
      ·
        refine ⟨545859865140391436453627921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 363906576760260957635751947 545859865140391436453627921)
        ·
          refine ⟨409394898855293577340220941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 545859865140391436453627921 409394898855293577340220941)
          ·
            refine ⟨153523087070735091502582853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 409394898855293577340220941 153523087070735091502582853)
            ·
              refine ⟨28785578825762829656734285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 153523087070735091502582853 28785578825762829656734285)
              ·
                refine ⟨10794592059661061121275357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28785578825762829656734285 10794592059661061121275357)
                ·
                  refine ⟨4047972022372897920478259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10794592059661061121275357 4047972022372897920478259)
                  ·
                    refine ⟨6071958033559346880717389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4047972022372897920478259 6071958033559346880717389)
                    ·
                      refine ⟨2276984262584755080269021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6071958033559346880717389 2276984262584755080269021)
                      ·
                        rfl

theorem cell23_4434411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3, 3, 1, 3].length) (baseStart_4434411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4434411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4434411 prefixEnd_4434411 := by exact prefixLift 4434411
  have htrace : WordTrace (prefixWord ++ tailWord_4434411) baseStart_4434411 baseEnd_4434411 := by
    simpa [prefixWord, tailWord_4434411, baseEnd_4434411] using wordTrace_append hprefix tailTrace_4434411
  have hstable : (prefixWord ++ tailWord_4434411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4434411).length < 2 ^ (prefixWord ++ tailWord_4434411).sum := by decide
  have hdescent : baseEnd_4434411 < baseStart_4434411 := by decide
  rcases family_descends (prefixWord ++ tailWord_4434411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4434451 : List Nat := [1, 1, 1, 2, 1, 5, 3, 3, 1, 1, 4]
def baseStart_4434451 : Nat := 118140960795 + 4434451 * 2 ^ 59
def prefixEnd_4434451 : Nat := 4983230072969 + 3 ^ 40 * 4434451 * 2
def baseEnd_4434451 : Nat := 2277004801810934923768837

theorem tailTrace_4434451 : CollatzResearch.WordTrace tailWord_4434451 prefixEnd_4434451 2277004801810934923768837 := by
  unfold tailWord_4434451
  simp only [CollatzResearch.WordTrace]
  refine ⟨161737715257748845780679207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107825143505165897187119471 161737715257748845780679207)
  ·
    refine ⟨242606572886623268671018811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161737715257748845780679207 242606572886623268671018811)
    ·
      refine ⟨363909859329934903006528217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242606572886623268671018811 363909859329934903006528217)
      ·
        refine ⟨272932394497451177254896163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 363909859329934903006528217 272932394497451177254896163)
        ·
          refine ⟨409398591746176765882344245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272932394497451177254896163 409398591746176765882344245)
          ·
            refine ⟨38381117976204071801469773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 409398591746176765882344245 38381117976204071801469773)
            ·
              refine ⟨14392919241076526925551165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38381117976204071801469773 14392919241076526925551165)
              ·
                refine ⟨5397344715403697597081687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14392919241076526925551165 5397344715403697597081687)
                ·
                  refine ⟨8096017073105546395622531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5397344715403697597081687 8096017073105546395622531)
                  ·
                    refine ⟨12144025609658319593433797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8096017073105546395622531 12144025609658319593433797)
                    ·
                      refine ⟨2277004801810934923768837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12144025609658319593433797 2277004801810934923768837)
                      ·
                        rfl

theorem cell23_4434451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 3, 1, 1, 4].length) (baseStart_4434451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4434451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4434451 prefixEnd_4434451 := by exact prefixLift 4434451
  have htrace : WordTrace (prefixWord ++ tailWord_4434451) baseStart_4434451 baseEnd_4434451 := by
    simpa [prefixWord, tailWord_4434451, baseEnd_4434451] using wordTrace_append hprefix tailTrace_4434451
  have hstable : (prefixWord ++ tailWord_4434451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4434451).length < 2 ^ (prefixWord ++ tailWord_4434451).sum := by decide
  have hdescent : baseEnd_4434451 < baseStart_4434451 := by decide
  rcases family_descends (prefixWord ++ tailWord_4434451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4434481 : List Nat := [1, 2, 2, 3, 1, 1, 5, 1, 1, 2, 4]
def baseStart_4434481 : Nat := 118140960795 + 4434481 * 2 ^ 59
def prefixEnd_4434481 : Nat := 4983230072969 + 3 ^ 40 * 4434481 * 2
def baseEnd_4434481 : Nat := 2277020206230569806393699

theorem tailTrace_4434481 : CollatzResearch.WordTrace tailWord_4434481 prefixEnd_4434481 2277020206230569806393699 := by
  unfold tailWord_4434481
  simp only [CollatzResearch.WordTrace]
  refine ⟨161738809447640160904271297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107825872965093440602847531 161738809447640160904271297)
  ·
    refine ⟨121304107085730120678203473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161738809447640160904271297 121304107085730120678203473)
    ·
      refine ⟨90978080314297590508652605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121304107085730120678203473 90978080314297590508652605)
      ·
        refine ⟨34116780117861596440744727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90978080314297590508652605 34116780117861596440744727)
        ·
          refine ⟨51175170176792394661117091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34116780117861596440744727 51175170176792394661117091)
          ·
            refine ⟨76762755265188591991675637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51175170176792394661117091 76762755265188591991675637)
            ·
              refine ⟨7196508306111430499219591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76762755265188591991675637 7196508306111430499219591)
              ·
                refine ⟨10794762459167145748829387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7196508306111430499219591 10794762459167145748829387)
                ·
                  refine ⟨16192143688750718623244081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10794762459167145748829387 16192143688750718623244081)
                  ·
                    refine ⟨12144107766563038967433061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16192143688750718623244081 12144107766563038967433061)
                    ·
                      refine ⟨2277020206230569806393699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12144107766563038967433061 2277020206230569806393699)
                      ·
                        rfl

theorem cell23_4434481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_4434481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4434481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4434481 prefixEnd_4434481 := by exact prefixLift 4434481
  have htrace : WordTrace (prefixWord ++ tailWord_4434481) baseStart_4434481 baseEnd_4434481 := by
    simpa [prefixWord, tailWord_4434481, baseEnd_4434481] using wordTrace_append hprefix tailTrace_4434481
  have hstable : (prefixWord ++ tailWord_4434481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4434481).length < 2 ^ (prefixWord ++ tailWord_4434481).sum := by decide
  have hdescent : baseEnd_4434481 < baseStart_4434481 := by decide
  rcases family_descends (prefixWord ++ tailWord_4434481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4434488 : List Nat := [2, 1, 2, 1, 4, 1, 4, 2, 1, 2, 3]
def baseStart_4434488 : Nat := 118140960795 + 4434488 * 2 ^ 59
def prefixEnd_4434488 : Nat := 4983230072969 + 3 ^ 40 * 4434488 * 2
def baseEnd_4434488 : Nat := 2277023800595151279006167

theorem tailTrace_4434488 : CollatzResearch.WordTrace tailWord_4434488 prefixEnd_4434488 2277023800595151279006167 := by
  unfold tailWord_4434488
  simp only [CollatzResearch.WordTrace]
  refine ⟨80869532379307400549888059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107826043172409867399850745 80869532379307400549888059)
  ·
    refine ⟨121304298568961100824832089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80869532379307400549888059 121304298568961100824832089)
    ·
      refine ⟨90978223926720825618624067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121304298568961100824832089 90978223926720825618624067)
      ·
        refine ⟨136467335890081238427936101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90978223926720825618624067 136467335890081238427936101)
        ·
          refine ⟨25587625479390232205238019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 136467335890081238427936101 25587625479390232205238019)
          ·
            refine ⟨38381438219085348307857029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25587625479390232205238019 38381438219085348307857029)
            ·
              refine ⟨7196519666078502807723193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38381438219085348307857029 7196519666078502807723193)
              ·
                refine ⟨5397389749558877105792395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7196519666078502807723193 5397389749558877105792395)
                ·
                  refine ⟨8096084624338315658688593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5397389749558877105792395 8096084624338315658688593)
                  ·
                    refine ⟨6072063468253736744016445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8096084624338315658688593 6072063468253736744016445)
                    ·
                      refine ⟨2277023800595151279006167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6072063468253736744016445 2277023800595151279006167)
                      ·
                        rfl

theorem cell23_4434488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 2, 1, 2, 3].length) (baseStart_4434488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4434488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4434488 prefixEnd_4434488 := by exact prefixLift 4434488
  have htrace : WordTrace (prefixWord ++ tailWord_4434488) baseStart_4434488 baseEnd_4434488 := by
    simpa [prefixWord, tailWord_4434488, baseEnd_4434488] using wordTrace_append hprefix tailTrace_4434488
  have hstable : (prefixWord ++ tailWord_4434488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4434488).length < 2 ^ (prefixWord ++ tailWord_4434488).sum := by decide
  have hdescent : baseEnd_4434488 < baseStart_4434488 := by decide
  rcases family_descends (prefixWord ++ tailWord_4434488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4434554 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 1, 5, 6]
def baseStart_4434554 : Nat := 118140960795 + 4434554 * 2 ^ 59
def prefixEnd_4434554 : Nat := 4983230072969 + 3 ^ 40 * 4434554 * 2
def baseEnd_4434554 : Nat := 2277057690318348020780863

theorem tailTrace_4434554 : CollatzResearch.WordTrace tailWord_4434554 prefixEnd_4434554 2277057690318348020780863 := by
  unfold tailWord_4434554
  simp only [CollatzResearch.WordTrace]
  refine ⟨40435367994093923592919679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107827647984250462914452477 40435367994093923592919679)
  ·
    refine ⟨60653051991140885389379519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40435367994093923592919679 60653051991140885389379519)
    ·
      refine ⟨90979577986711328084069279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60653051991140885389379519 90979577986711328084069279)
      ·
        refine ⟨136469366980066992126103919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90979577986711328084069279 136469366980066992126103919)
        ·
          refine ⟨204704050470100488189155879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136469366980066992126103919 204704050470100488189155879)
          ·
            refine ⟨307056075705150732283733819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204704050470100488189155879 307056075705150732283733819)
            ·
              refine ⟨460584113557726098425600729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 307056075705150732283733819 460584113557726098425600729)
              ·
                refine ⟨345438085168294573819200547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 460584113557726098425600729 345438085168294573819200547)
                ·
                  refine ⟨518157127752441860728800821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 345438085168294573819200547 518157127752441860728800821)
                  ·
                    refine ⟨48577230726791424443325077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 518157127752441860728800821 48577230726791424443325077)
                    ·
                      refine ⟨2277057690318348020780863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48577230726791424443325077 2277057690318348020780863)
                      ·
                        rfl

theorem cell23_4434554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 1, 5, 6].length) (baseStart_4434554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4434554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4434554 prefixEnd_4434554 := by exact prefixLift 4434554
  have htrace : WordTrace (prefixWord ++ tailWord_4434554) baseStart_4434554 baseEnd_4434554 := by
    simpa [prefixWord, tailWord_4434554, baseEnd_4434554] using wordTrace_append hprefix tailTrace_4434554
  have hstable : (prefixWord ++ tailWord_4434554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4434554).length < 2 ^ (prefixWord ++ tailWord_4434554).sum := by decide
  have hdescent : baseEnd_4434554 < baseStart_4434554 := by decide
  rcases family_descends (prefixWord ++ tailWord_4434554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4434561 : List Nat := [1, 2, 4, 2, 1, 1, 1, 3, 2, 1, 5]
def baseStart_4434561 : Nat := 118140960795 + 4434561 * 2 ^ 59
def prefixEnd_4434561 : Nat := 4983230072969 + 3 ^ 40 * 4434561 * 2
def baseEnd_4434561 : Nat := 2277061284682929493393331

theorem tailTrace_4434561 : CollatzResearch.WordTrace tailWord_4434561 prefixEnd_4434561 2277061284682929493393331 := by
  unfold tailWord_4434561
  simp only [CollatzResearch.WordTrace]
  refine ⟨161741727287350334567183537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107827818191566889711455691 161741727287350334567183537)
  ·
    refine ⟨121306295465512750925387653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161741727287350334567183537 121306295465512750925387653)
    ·
      refine ⟨22744930399783640798510185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121306295465512750925387653 22744930399783640798510185)
      ·
        refine ⟨17058697799837730598882639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22744930399783640798510185 17058697799837730598882639)
        ·
          refine ⟨25588046699756595898323959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17058697799837730598882639 25588046699756595898323959)
          ·
            refine ⟨38382070049634893847485939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25588046699756595898323959 38382070049634893847485939)
            ·
              refine ⟨57573105074452340771228909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38382070049634893847485939 57573105074452340771228909)
              ·
                refine ⟨21589914402919627789210841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57573105074452340771228909 21589914402919627789210841)
                ·
                  refine ⟨16192435802189720841908131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21589914402919627789210841 16192435802189720841908131)
                  ·
                    refine ⟨24288653703284581262862197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16192435802189720841908131 24288653703284581262862197)
                    ·
                      refine ⟨2277061284682929493393331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24288653703284581262862197 2277061284682929493393331)
                      ·
                        rfl

theorem cell23_4434561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_4434561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4434561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4434561 prefixEnd_4434561 := by exact prefixLift 4434561
  have htrace : WordTrace (prefixWord ++ tailWord_4434561) baseStart_4434561 baseEnd_4434561 := by
    simpa [prefixWord, tailWord_4434561, baseEnd_4434561] using wordTrace_append hprefix tailTrace_4434561
  have hstable : (prefixWord ++ tailWord_4434561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4434561).length < 2 ^ (prefixWord ++ tailWord_4434561).sum := by decide
  have hdescent : baseEnd_4434561 < baseStart_4434561 := by decide
  rcases family_descends (prefixWord ++ tailWord_4434561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4434578 : List Nat := [3, 2, 3, 1, 2, 1, 1, 1, 2, 4, 3]
def baseStart_4434578 : Nat := 118140960795 + 4434578 * 2 ^ 59
def prefixEnd_4434578 : Nat := 4983230072969 + 3 ^ 40 * 4434578 * 2
def baseEnd_4434578 : Nat := 2277070013854055926880753

theorem tailTrace_4434578 : CollatzResearch.WordTrace tailWord_4434578 prefixEnd_4434578 2277070013854055926880753 := by
  unfold tailWord_4434578
  simp only [CollatzResearch.WordTrace]
  refine ⟨40435586832072186617638097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107828231552192497647034925 40435586832072186617638097)
  ·
    refine ⟨30326690124054139963228573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40435586832072186617638097 30326690124054139963228573)
    ·
      refine ⟨11372508796520302486210715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30326690124054139963228573 11372508796520302486210715)
      ·
        refine ⟨17058763194780453729316073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11372508796520302486210715 17058763194780453729316073)
        ·
          refine ⟨12794072396085340296987055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17058763194780453729316073 12794072396085340296987055)
          ·
            refine ⟨19191108594128010445480583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12794072396085340296987055 19191108594128010445480583)
            ·
              refine ⟨28786662891192015668220875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19191108594128010445480583 28786662891192015668220875)
              ·
                refine ⟨43179994336788023502331313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28786662891192015668220875 43179994336788023502331313)
                ·
                  refine ⟨32384995752591017626748485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43179994336788023502331313 32384995752591017626748485)
                  ·
                    refine ⟨6072186703610815805015341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32384995752591017626748485 6072186703610815805015341)
                    ·
                      refine ⟨2277070013854055926880753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6072186703610815805015341 2277070013854055926880753)
                      ·
                        rfl

theorem cell23_4434578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_4434578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4434578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4434578 prefixEnd_4434578 := by exact prefixLift 4434578
  have htrace : WordTrace (prefixWord ++ tailWord_4434578) baseStart_4434578 baseEnd_4434578 := by
    simpa [prefixWord, tailWord_4434578, baseEnd_4434578] using wordTrace_append hprefix tailTrace_4434578
  have hstable : (prefixWord ++ tailWord_4434578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4434578).length < 2 ^ (prefixWord ++ tailWord_4434578).sum := by decide
  have hdescent : baseEnd_4434578 < baseStart_4434578 := by decide
  rcases family_descends (prefixWord ++ tailWord_4434578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4434588 : List Nat := [2, 2, 3, 2, 2, 2, 1, 1, 2, 2, 4]
def baseStart_4434588 : Nat := 118140960795 + 4434588 * 2 ^ 59
def prefixEnd_4434588 : Nat := 4983230072969 + 3 ^ 40 * 4434588 * 2
def baseEnd_4434588 : Nat := 2277075148660600887755707

theorem tailTrace_4434588 : CollatzResearch.WordTrace tailWord_4434588 prefixEnd_4434588 2277075148660600887755707 := by
  unfold tailWord_4434588
  simp only [CollatzResearch.WordTrace]
  refine ⟨80871356029126259089208209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107828474705501678785610945 80871356029126259089208209)
  ·
    refine ⟨60653517021844694316906157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80871356029126259089208209 60653517021844694316906157)
    ·
      refine ⟨22745068883191760368839809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60653517021844694316906157 22745068883191760368839809)
      ·
        refine ⟨17058801662393820276629857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22745068883191760368839809 17058801662393820276629857)
        ·
          refine ⟨12794101246795365207472393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17058801662393820276629857 12794101246795365207472393)
          ·
            refine ⟨9595575935096523905604295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12794101246795365207472393 9595575935096523905604295)
            ·
              refine ⟨14393363902644785858406443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9595575935096523905604295 14393363902644785858406443)
              ·
                refine ⟨21590045853967178787609665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14393363902644785858406443 21590045853967178787609665)
                ·
                  refine ⟨16192534390475384090707249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21590045853967178787609665 16192534390475384090707249)
                  ·
                    refine ⟨12144400792856538068030437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16192534390475384090707249 12144400792856538068030437)
                    ·
                      refine ⟨2277075148660600887755707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12144400792856538068030437 2277075148660600887755707)
                      ·
                        rfl

theorem cell23_4434588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_4434588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4434588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4434588 prefixEnd_4434588 := by exact prefixLift 4434588
  have htrace : WordTrace (prefixWord ++ tailWord_4434588) baseStart_4434588 baseEnd_4434588 := by
    simpa [prefixWord, tailWord_4434588, baseEnd_4434588] using wordTrace_append hprefix tailTrace_4434588
  have hstable : (prefixWord ++ tailWord_4434588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4434588).length < 2 ^ (prefixWord ++ tailWord_4434588).sum := by decide
  have hdescent : baseEnd_4434588 < baseStart_4434588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4434588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4434611 : List Nat := [1, 1, 1, 2, 3, 5, 1, 1, 1, 7]
def baseStart_4434611 : Nat := 118140960795 + 4434611 * 2 ^ 59
def prefixEnd_4434611 : Nat := 4983230072969 + 3 ^ 40 * 4434611 * 2
def baseEnd_4434611 : Nat := 759028986238551432589367

theorem tailTrace_4434611 : CollatzResearch.WordTrace tailWord_4434611 prefixEnd_4434611 759028986238551432589367 := by
  unfold tailWord_4434611
  simp only [CollatzResearch.WordTrace]
  refine ⟨161743550937169193106503687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107829033958112795404335791 161743550937169193106503687)
  ·
    refine ⟨242615326405753789659755531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161743550937169193106503687 242615326405753789659755531)
    ·
      refine ⟨363922989608630684489633297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242615326405753789659755531 363922989608630684489633297)
      ·
        refine ⟨272942242206473013367224973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 363922989608630684489633297 272942242206473013367224973)
        ·
          refine ⟨102353340827427380012709365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 272942242206473013367224973 102353340827427380012709365)
          ·
            refine ⟨9595625702571316876191503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 102353340827427380012709365 9595625702571316876191503)
            ·
              refine ⟨14393438553856975314287255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9595625702571316876191503 14393438553856975314287255)
              ·
                refine ⟨21590157830785462971430883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14393438553856975314287255 21590157830785462971430883)
                ·
                  refine ⟨32385236746178194457146325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21590157830785462971430883 32385236746178194457146325)
                  ·
                    refine ⟨759028986238551432589367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32385236746178194457146325 759028986238551432589367)
                    ·
                      rfl

theorem cell23_4434611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 7].length) (baseStart_4434611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4434611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4434611 prefixEnd_4434611 := by exact prefixLift 4434611
  have htrace : WordTrace (prefixWord ++ tailWord_4434611) baseStart_4434611 baseEnd_4434611 := by
    simpa [prefixWord, tailWord_4434611, baseEnd_4434611] using wordTrace_append hprefix tailTrace_4434611
  have hstable : (prefixWord ++ tailWord_4434611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4434611).length < 2 ^ (prefixWord ++ tailWord_4434611).sum := by decide
  have hdescent : baseEnd_4434611 < baseStart_4434611 := by decide
  rcases family_descends (prefixWord ++ tailWord_4434611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4434615 : List Nat := [1, 1, 3, 1, 6, 1, 2, 3, 5]
def baseStart_4434615 : Nat := 118140960795 + 4434615 * 2 ^ 59
def prefixEnd_4434615 : Nat := 4983230072969 + 3 ^ 40 * 4434615 * 2
def baseEnd_4434615 : Nat := 253009890293141364679787

theorem tailTrace_4434615 : CollatzResearch.WordTrace tailWord_4434615 prefixEnd_4434615 253009890293141364679787 := by
  unfold tailWord_4434615
  simp only [CollatzResearch.WordTrace]
  refine ⟨161743696829154701789649299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107829131219436467859766199 161743696829154701789649299)
  ·
    refine ⟨242615545243732052684473949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161743696829154701789649299 242615545243732052684473949)
    ·
      refine ⟨90980829466399519756677731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 242615545243732052684473949 90980829466399519756677731)
      ·
        refine ⟨136471244199599279635016597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90980829466399519756677731 136471244199599279635016597)
        ·
          refine ⟨6397089571856216232891403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 136471244199599279635016597 6397089571856216232891403)
          ·
            refine ⟨9595634357784324349337105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6397089571856216232891403 9595634357784324349337105)
            ·
              refine ⟨7196725768338243262002829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9595634357784324349337105 7196725768338243262002829)
              ·
                refine ⟨2698772163126841223251061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7196725768338243262002829 2698772163126841223251061)
                ·
                  refine ⟨253009890293141364679787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2698772163126841223251061 253009890293141364679787)
                  ·
                    rfl

theorem cell23_4434615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 3, 5].length) (baseStart_4434615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4434615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4434615 prefixEnd_4434615 := by exact prefixLift 4434615
  have htrace : WordTrace (prefixWord ++ tailWord_4434615) baseStart_4434615 baseEnd_4434615 := by
    simpa [prefixWord, tailWord_4434615, baseEnd_4434615] using wordTrace_append hprefix tailTrace_4434615
  have hstable : (prefixWord ++ tailWord_4434615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4434615).length < 2 ^ (prefixWord ++ tailWord_4434615).sum := by decide
  have hdescent : baseEnd_4434615 < baseStart_4434615 := by decide
  rcases family_descends (prefixWord ++ tailWord_4434615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4434668 : List Nat := [2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 3]
def baseStart_4434668 : Nat := 118140960795 + 4434668 * 2 ^ 59
def prefixEnd_4434668 : Nat := 4983230072969 + 3 ^ 40 * 4434668 * 2
def baseEnd_4434668 : Nat := 2277116227112960574755339

theorem tailTrace_4434668 : CollatzResearch.WordTrace tailWord_4434668 prefixEnd_4434668 2277116227112960574755339 := by
  unfold tailWord_4434668
  simp only [CollatzResearch.WordTrace]
  refine ⟨80872814948981345920664329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107830419931975127894219105 80872814948981345920664329)
  ·
    refine ⟨60654611211736009440498247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80872814948981345920664329 60654611211736009440498247)
    ·
      refine ⟨90981916817604014160747371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60654611211736009440498247 90981916817604014160747371)
      ·
        refine ⟨136472875226406021241121057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90981916817604014160747371 136472875226406021241121057)
        ·
          refine ⟨102354656419804515930840793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136472875226406021241121057 102354656419804515930840793)
          ·
            refine ⟨76765992314853386948130595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102354656419804515930840793 76765992314853386948130595)
            ·
              refine ⟨115148988472280080422195893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76765992314853386948130595 115148988472280080422195893)
              ·
                refine ⟨10795217669276257539580865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 115148988472280080422195893 10795217669276257539580865)
                ·
                  refine ⟨8096413251957193154685649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10795217669276257539580865 8096413251957193154685649)
                  ·
                    refine ⟨6072309938967894866014237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8096413251957193154685649 6072309938967894866014237)
                    ·
                      refine ⟨2277116227112960574755339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6072309938967894866014237 2277116227112960574755339)
                      ·
                        rfl

theorem cell23_4434668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 3].length) (baseStart_4434668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4434668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4434668 prefixEnd_4434668 := by exact prefixLift 4434668
  have htrace : WordTrace (prefixWord ++ tailWord_4434668) baseStart_4434668 baseEnd_4434668 := by
    simpa [prefixWord, tailWord_4434668, baseEnd_4434668] using wordTrace_append hprefix tailTrace_4434668
  have hstable : (prefixWord ++ tailWord_4434668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4434668).length < 2 ^ (prefixWord ++ tailWord_4434668).sum := by decide
  have hdescent : baseEnd_4434668 < baseStart_4434668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4434668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4434671 : List Nat := [1, 1, 2, 1, 5, 2, 1, 2, 8]
def baseStart_4434671 : Nat := 118140960795 + 4434671 * 2 ^ 59
def prefixEnd_4434671 : Nat := 4983230072969 + 3 ^ 40 * 4434671 * 2
def baseEnd_4434671 : Nat := 253013085283880451446425

theorem tailTrace_4434671 : CollatzResearch.WordTrace tailWord_4434671 prefixEnd_4434671 253013085283880451446425 := by
  unfold tailWord_4434671
  simp only [CollatzResearch.WordTrace]
  refine ⟨161745739316951823353687867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107830492877967882235791911 161745739316951823353687867)
  ·
    refine ⟨242618608975427735030531801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161745739316951823353687867 242618608975427735030531801)
    ·
      refine ⟨181963956731570801272898851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 242618608975427735030531801 181963956731570801272898851)
      ·
        refine ⟨272945935097356201909348277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181963956731570801272898851 272945935097356201909348277)
        ·
          refine ⟨25588681415377143929001401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 272945935097356201909348277 25588681415377143929001401)
          ·
            refine ⟨19191511061532857946751051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25588681415377143929001401 19191511061532857946751051)
            ·
              refine ⟨28787266592299286920126577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19191511061532857946751051 28787266592299286920126577)
              ·
                refine ⟨21590449944224465190094933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28787266592299286920126577 21590449944224465190094933)
                ·
                  refine ⟨253013085283880451446425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21590449944224465190094933 253013085283880451446425)
                  ·
                    rfl

theorem cell23_4434671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 8].length) (baseStart_4434671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4434671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4434671 prefixEnd_4434671 := by exact prefixLift 4434671
  have htrace : WordTrace (prefixWord ++ tailWord_4434671) baseStart_4434671 baseEnd_4434671 := by
    simpa [prefixWord, tailWord_4434671, baseEnd_4434671] using wordTrace_append hprefix tailTrace_4434671
  have hstable : (prefixWord ++ tailWord_4434671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4434671).length < 2 ^ (prefixWord ++ tailWord_4434671).sum := by decide
  have hdescent : baseEnd_4434671 < baseStart_4434671 := by decide
  rcases family_descends (prefixWord ++ tailWord_4434671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4434731 : List Nat := [1, 1, 1, 1, 2, 1, 2, 5, 3, 6]
def baseStart_4434731 : Nat := 118140960795 + 4434731 * 2 ^ 59
def prefixEnd_4434731 : Nat := 4983230072969 + 3 ^ 40 * 4434731 * 2
def baseEnd_4434731 : Nat := 759049525464731276089183

theorem tailTrace_4434731 : CollatzResearch.WordTrace tailWord_4434731 prefixEnd_4434731 759049525464731276089183 := by
  unfold tailWord_4434731
  simp only [CollatzResearch.WordTrace]
  refine ⟨161747927696734453600872047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107831951797822969067248031 161747927696734453600872047)
  ·
    refine ⟨242621891545101680401308071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161747927696734453600872047 242621891545101680401308071)
    ·
      refine ⟨363932837317652520601962107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242621891545101680401308071 363932837317652520601962107)
      ·
        refine ⟨545899255976478780902943161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 363932837317652520601962107 545899255976478780902943161)
        ·
          refine ⟨409424441982359085677207371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 545899255976478780902943161 409424441982359085677207371)
          ·
            refine ⟨614136662973538628515811057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 409424441982359085677207371 614136662973538628515811057)
            ·
              refine ⟨460602497230153971386858293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 614136662973538628515811057 460602497230153971386858293)
              ·
                refine ⟨43181484115326934817517965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 460602497230153971386858293 43181484115326934817517965)
                ·
                  refine ⟨16193056543247600556569237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43181484115326934817517965 16193056543247600556569237)
                  ·
                    refine ⟨759049525464731276089183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16193056543247600556569237 759049525464731276089183)
                    ·
                      rfl

theorem cell23_4434731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3, 6].length) (baseStart_4434731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4434731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4434731 prefixEnd_4434731 := by exact prefixLift 4434731
  have htrace : WordTrace (prefixWord ++ tailWord_4434731) baseStart_4434731 baseEnd_4434731 := by
    simpa [prefixWord, tailWord_4434731, baseEnd_4434731] using wordTrace_append hprefix tailTrace_4434731
  have hstable : (prefixWord ++ tailWord_4434731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4434731).length < 2 ^ (prefixWord ++ tailWord_4434731).sum := by decide
  have hdescent : baseEnd_4434731 < baseStart_4434731 := by decide
  rcases family_descends (prefixWord ++ tailWord_4434731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4434732 : List Nat := [2, 2, 1, 1, 1, 4, 2, 5, 1, 1, 3]
def baseStart_4434732 : Nat := 118140960795 + 4434732 * 2 ^ 59
def prefixEnd_4434732 : Nat := 4983230072969 + 3 ^ 40 * 4434732 * 2
def baseEnd_4434732 : Nat := 2277149089874848324355045

theorem tailTrace_4434732 : CollatzResearch.WordTrace tailWord_4434732 prefixEnd_4434732 2277149089874848324355045 := by
  unfold tailWord_4434732
  simp only [CollatzResearch.WordTrace]
  refine ⟨80873982084865415385829225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107831976113153887181105633 80873982084865415385829225)
  ·
    refine ⟨60655486563649061539371919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80873982084865415385829225 60655486563649061539371919)
    ·
      refine ⟨90983229845473592309057879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60655486563649061539371919 90983229845473592309057879)
      ·
        refine ⟨136474844768210388463586819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90983229845473592309057879 136474844768210388463586819)
        ·
          refine ⟨204712267152315582695380229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136474844768210388463586819 204712267152315582695380229)
          ·
            refine ⟨38383550091059171755383793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 204712267152315582695380229 38383550091059171755383793)
            ·
              refine ⟨28787662568294378816537845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38383550091059171755383793 28787662568294378816537845)
              ·
                refine ⟨2698843365777598014050423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28787662568294378816537845 2698843365777598014050423)
                ·
                  refine ⟨4048265048666397021075635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2698843365777598014050423 4048265048666397021075635)
                  ·
                    refine ⟨6072397572999595531613453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4048265048666397021075635 6072397572999595531613453)
                    ·
                      refine ⟨2277149089874848324355045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6072397572999595531613453 2277149089874848324355045)
                      ·
                        rfl

theorem cell23_4434732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 5, 1, 1, 3].length) (baseStart_4434732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4434732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4434732 prefixEnd_4434732 := by exact prefixLift 4434732
  have htrace : WordTrace (prefixWord ++ tailWord_4434732) baseStart_4434732 baseEnd_4434732 := by
    simpa [prefixWord, tailWord_4434732, baseEnd_4434732] using wordTrace_append hprefix tailTrace_4434732
  have hstable : (prefixWord ++ tailWord_4434732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4434732).length < 2 ^ (prefixWord ++ tailWord_4434732).sum := by decide
  have hdescent : baseEnd_4434732 < baseStart_4434732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4434732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4434768 : List Nat := [2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 4]
def baseStart_4434768 : Nat := 118140960795 + 4434768 * 2 ^ 59
def prefixEnd_4434768 : Nat := 4983230072969 + 3 ^ 40 * 4434768 * 2
def baseEnd_4434768 : Nat := 2277167575178410183504879

theorem tailTrace_4434768 : CollatzResearch.WordTrace tailWord_4434768 prefixEnd_4434768 2277167575178410183504879 := by
  unfold tailWord_4434768
  simp only [CollatzResearch.WordTrace]
  refine ⟨80874638598800204459984479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107832851465066939279979305 80874638598800204459984479)
  ·
    refine ⟨121311957898200306689976719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80874638598800204459984479 121311957898200306689976719)
    ·
      refine ⟨181967936847300460034965079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121311957898200306689976719 181967936847300460034965079)
      ·
        refine ⟨272951905270950690052447619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181967936847300460034965079 272951905270950690052447619)
        ·
          refine ⟨409427857906426035078671429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272951905270950690052447619 409427857906426035078671429)
          ·
            refine ⟨76767723357454881577250893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 409427857906426035078671429 76767723357454881577250893)
            ·
              refine ⟨28787896259045580591469085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76767723357454881577250893 28787896259045580591469085)
              ·
                refine ⟨10795461097142092721800907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28787896259045580591469085 10795461097142092721800907)
                ·
                  refine ⟨16193191645713139082701361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10795461097142092721800907 16193191645713139082701361)
                  ·
                    refine ⟨12144893734284854312026021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16193191645713139082701361 12144893734284854312026021)
                    ·
                      refine ⟨2277167575178410183504879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12144893734284854312026021 2277167575178410183504879)
                      ·
                        rfl

theorem cell23_4434768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 4].length) (baseStart_4434768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4434768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4434768 prefixEnd_4434768 := by exact prefixLift 4434768
  have htrace : WordTrace (prefixWord ++ tailWord_4434768) baseStart_4434768 baseEnd_4434768 := by
    simpa [prefixWord, tailWord_4434768, baseEnd_4434768] using wordTrace_append hprefix tailTrace_4434768
  have hstable : (prefixWord ++ tailWord_4434768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4434768).length < 2 ^ (prefixWord ++ tailWord_4434768).sum := by decide
  have hdescent : baseEnd_4434768 < baseStart_4434768 := by decide
  rcases family_descends (prefixWord ++ tailWord_4434768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4434771 : List Nat := [1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 7]
def baseStart_4434771 : Nat := 118140960795 + 4434771 * 2 ^ 59
def prefixEnd_4434771 : Nat := 4983230072969 + 3 ^ 40 * 4434771 * 2
def baseEnd_4434771 : Nat := 2277169115620373671767365

theorem tailTrace_4434771 : CollatzResearch.WordTrace tailWord_4434771 prefixEnd_4434771 2277169115620373671767365 := by
  unfold tailWord_4434771
  simp only [CollatzResearch.WordTrace]
  refine ⟨161749386616589540432328167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107832924411059693621552111 161749386616589540432328167)
  ·
    refine ⟨242624079924884310648492251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161749386616589540432328167 242624079924884310648492251)
    ·
      refine ⟨363936119887326465972738377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242624079924884310648492251 363936119887326465972738377)
      ·
        refine ⟨272952089915494849479553783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 363936119887326465972738377 272952089915494849479553783)
        ·
          refine ⟨409428134873242274219330675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272952089915494849479553783 409428134873242274219330675)
          ·
            refine ⟨614142202309863411328996013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 409428134873242274219330675 614142202309863411328996013)
            ·
              refine ⟨230303325866198779248373505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 614142202309863411328996013 230303325866198779248373505)
              ·
                refine ⟨172727494399649084436280129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 230303325866198779248373505 172727494399649084436280129)
                ·
                  refine ⟨129545620799736813327210097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 172727494399649084436280129 129545620799736813327210097)
                  ·
                    refine ⟨97159215599802609995407573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 129545620799736813327210097 97159215599802609995407573)
                    ·
                      refine ⟨2277169115620373671767365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 97159215599802609995407573 2277169115620373671767365)
                      ·
                        rfl

theorem cell23_4434771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 7].length) (baseStart_4434771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4434771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4434771 prefixEnd_4434771 := by exact prefixLift 4434771
  have htrace : WordTrace (prefixWord ++ tailWord_4434771) baseStart_4434771 baseEnd_4434771 := by
    simpa [prefixWord, tailWord_4434771, baseEnd_4434771] using wordTrace_append hprefix tailTrace_4434771
  have hstable : (prefixWord ++ tailWord_4434771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4434771).length < 2 ^ (prefixWord ++ tailWord_4434771).sum := by decide
  have hdescent : baseEnd_4434771 < baseStart_4434771 := by decide
  rcases family_descends (prefixWord ++ tailWord_4434771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4434775 : List Nat := [1, 1, 3, 2, 4, 1, 2, 1, 3, 2, 3]
def baseStart_4434775 : Nat := 118140960795 + 4434775 * 2 ^ 59
def prefixEnd_4434775 : Nat := 4983230072969 + 3 ^ 40 * 4434775 * 2
def baseEnd_4434775 : Nat := 2277171169542991656117347

theorem tailTrace_4434775 : CollatzResearch.WordTrace tailWord_4434775 prefixEnd_4434775 2277171169542991656117347 := by
  unfold tailWord_4434775
  simp only [CollatzResearch.WordTrace]
  refine ⟨161749532508575049115473779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107833021672383366076982519 161749532508575049115473779)
  ·
    refine ⟨242624298762862573673210669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161749532508575049115473779 242624298762862573673210669)
    ·
      refine ⟨90984112036073465127454001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 242624298762862573673210669 90984112036073465127454001)
      ·
        refine ⟨68238084027055098845590501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90984112036073465127454001 68238084027055098845590501)
        ·
          refine ⟨12794640755072831033548219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68238084027055098845590501 12794640755072831033548219)
          ·
            refine ⟨19191961132609246550322329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12794640755072831033548219 19191961132609246550322329)
            ·
              refine ⟨14393970849456934912741747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19191961132609246550322329 14393970849456934912741747)
              ·
                refine ⟨21590956274185402369112621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14393970849456934912741747 21590956274185402369112621)
                ·
                  refine ⟨8096608602819525888417233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21590956274185402369112621 8096608602819525888417233)
                  ·
                    refine ⟨6072456452114644416312925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8096608602819525888417233 6072456452114644416312925)
                    ·
                      refine ⟨2277171169542991656117347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6072456452114644416312925 2277171169542991656117347)
                      ·
                        rfl

theorem cell23_4434775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 3, 2, 3].length) (baseStart_4434775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4434775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4434775 prefixEnd_4434775 := by exact prefixLift 4434775
  have htrace : WordTrace (prefixWord ++ tailWord_4434775) baseStart_4434775 baseEnd_4434775 := by
    simpa [prefixWord, tailWord_4434775, baseEnd_4434775] using wordTrace_append hprefix tailTrace_4434775
  have hstable : (prefixWord ++ tailWord_4434775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4434775).length < 2 ^ (prefixWord ++ tailWord_4434775).sum := by decide
  have hdescent : baseEnd_4434775 < baseStart_4434775 := by decide
  rcases family_descends (prefixWord ++ tailWord_4434775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4434786 : List Nat := [3, 3, 2, 1, 4, 1, 2, 1, 1, 5]
def baseStart_4434786 : Nat := 118140960795 + 4434786 * 2 ^ 59
def prefixEnd_4434786 : Nat := 4983230072969 + 3 ^ 40 * 4434786 * 2
def baseEnd_4434786 : Nat := 759058939276730371026599

theorem tailTrace_4434786 : CollatzResearch.WordTrace tailWord_4434786 prefixEnd_4434786 759058939276730371026599 := by
  unfold tailWord_4434786
  simp only [CollatzResearch.WordTrace]
  refine ⟨40437483427883799498531053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107833289141023465329416141 40437483427883799498531053)
  ·
    refine ⟨15164056285456424811949145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40437483427883799498531053 15164056285456424811949145)
    ·
      refine ⟨11373042214092318608961859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15164056285456424811949145 11373042214092318608961859)
      ·
        refine ⟨17059563321138477913442789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11373042214092318608961859 17059563321138477913442789)
        ·
          refine ⟨3198668122713464608770523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17059563321138477913442789 3198668122713464608770523)
          ·
            refine ⟨4798002184070196913155785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3198668122713464608770523 4798002184070196913155785)
            ·
              refine ⟨3598501638052647684866839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4798002184070196913155785 3598501638052647684866839)
              ·
                refine ⟨5397752457078971527300259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3598501638052647684866839 5397752457078971527300259)
                ·
                  refine ⟨8096628685618457290950389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5397752457078971527300259 8096628685618457290950389)
                  ·
                    refine ⟨759058939276730371026599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8096628685618457290950389 759058939276730371026599)
                    ·
                      rfl

theorem cell23_4434786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_4434786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4434786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4434786 prefixEnd_4434786 := by exact prefixLift 4434786
  have htrace : WordTrace (prefixWord ++ tailWord_4434786) baseStart_4434786 baseEnd_4434786 := by
    simpa [prefixWord, tailWord_4434786, baseEnd_4434786] using wordTrace_append hprefix tailTrace_4434786
  have hstable : (prefixWord ++ tailWord_4434786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4434786).length < 2 ^ (prefixWord ++ tailWord_4434786).sum := by decide
  have hdescent : baseEnd_4434786 < baseStart_4434786 := by decide
  rcases family_descends (prefixWord ++ tailWord_4434786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4434789 : List Nat := [1, 3, 1, 3, 1, 1, 3, 5, 1, 2, 2]
def baseStart_4434789 : Nat := 118140960795 + 4434789 * 2 ^ 59
def prefixEnd_4434789 : Nat := 4983230072969 + 3 ^ 40 * 4434789 * 2
def baseEnd_4434789 : Nat := 2277178358272154601342283

theorem tailTrace_4434789 : CollatzResearch.WordTrace tailWord_4434789 prefixEnd_4434789 2277178358272154601342283 := by
  unfold tailWord_4434789
  simp only [CollatzResearch.WordTrace]
  refine ⟨161750043130524329506483421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107833362087016219670988947 161750043130524329506483421)
  ·
    refine ⟨60656266173946623564931283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161750043130524329506483421 60656266173946623564931283)
    ·
      refine ⟨90984399260919935347396925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60656266173946623564931283 90984399260919935347396925)
      ·
        refine ⟨34119149722844975755273847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90984399260919935347396925 34119149722844975755273847)
        ·
          refine ⟨51178724584267463632910771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34119149722844975755273847 51178724584267463632910771)
          ·
            refine ⟨76768086876401195449366157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51178724584267463632910771 76768086876401195449366157)
            ·
              refine ⟨28788032578650448293512309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76768086876401195449366157 28788032578650448293512309)
              ·
                refine ⟨2698878054248479527516779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28788032578650448293512309 2698878054248479527516779)
                ·
                  refine ⟨4048317081372719291275169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2698878054248479527516779 4048317081372719291275169)
                  ·
                    refine ⟨3036237811029539468456377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4048317081372719291275169 3036237811029539468456377)
                    ·
                      refine ⟨2277178358272154601342283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3036237811029539468456377 2277178358272154601342283)
                      ·
                        rfl

theorem cell23_4434789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 5, 1, 2, 2].length) (baseStart_4434789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4434789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4434789 prefixEnd_4434789 := by exact prefixLift 4434789
  have htrace : WordTrace (prefixWord ++ tailWord_4434789) baseStart_4434789 baseEnd_4434789 := by
    simpa [prefixWord, tailWord_4434789, baseEnd_4434789] using wordTrace_append hprefix tailTrace_4434789
  have hstable : (prefixWord ++ tailWord_4434789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4434789).length < 2 ^ (prefixWord ++ tailWord_4434789).sum := by decide
  have hdescent : baseEnd_4434789 < baseStart_4434789 := by decide
  rcases family_descends (prefixWord ++ tailWord_4434789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4434792 : List Nat := [2, 1, 4, 2, 1, 3, 1, 3, 1, 2, 3]
def baseStart_4434792 : Nat := 118140960795 + 4434792 * 2 ^ 59
def prefixEnd_4434792 : Nat := 4983230072969 + 3 ^ 40 * 4434792 * 2
def baseEnd_4434792 : Nat := 2277179898714118089604769

theorem tailTrace_4434792 : CollatzResearch.WordTrace tailWord_4434792 prefixEnd_4434792 2277179898714118089604769 := by
  unfold tailWord_4434792
  simp only [CollatzResearch.WordTrace]
  refine ⟨80875076274756730509421315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107833435033008974012561753 80875076274756730509421315)
  ·
    refine ⟨121312614412135095764131973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80875076274756730509421315 121312614412135095764131973)
    ·
      refine ⟨22746115202275330455774745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121312614412135095764131973 22746115202275330455774745)
      ·
        refine ⟨17059586401706497841831059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22746115202275330455774745 17059586401706497841831059)
        ·
          refine ⟨25589379602559746762746589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17059586401706497841831059 25589379602559746762746589)
          ·
            refine ⟨9596017350959905036029971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25589379602559746762746589 9596017350959905036029971)
            ·
              refine ⟨14394026026439857554044957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9596017350959905036029971 14394026026439857554044957)
              ·
                refine ⟨5397759759914946582766859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14394026026439857554044957 5397759759914946582766859)
                ·
                  refine ⟨8096639639872419874150289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5397759759914946582766859 8096639639872419874150289)
                  ·
                    refine ⟨6072479729904314905612717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8096639639872419874150289 6072479729904314905612717)
                    ·
                      refine ⟨2277179898714118089604769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6072479729904314905612717 2277179898714118089604769)
                      ·
                        rfl

theorem cell23_4434792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_4434792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4434792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4434792 prefixEnd_4434792 := by exact prefixLift 4434792
  have htrace : WordTrace (prefixWord ++ tailWord_4434792) baseStart_4434792 baseEnd_4434792 := by
    simpa [prefixWord, tailWord_4434792, baseEnd_4434792] using wordTrace_append hprefix tailTrace_4434792
  have hstable : (prefixWord ++ tailWord_4434792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4434792).length < 2 ^ (prefixWord ++ tailWord_4434792).sum := by decide
  have hdescent : baseEnd_4434792 < baseStart_4434792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4434792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4434806 : List Nat := [5, 1, 1, 3, 1, 2, 2, 1, 3, 2, 2]
def baseStart_4434806 : Nat := 118140960795 + 4434806 * 2 ^ 59
def prefixEnd_4434806 : Nat := 4983230072969 + 3 ^ 40 * 4434806 * 2
def baseEnd_4434806 : Nat := 2277187087443281034829705

theorem tailTrace_4434806 : CollatzResearch.WordTrace tailWord_4434806 prefixEnd_4434806 2277187087443281034829705 := by
  unfold tailWord_4434806
  simp only [CollatzResearch.WordTrace]
  refine ⟨10109416448216421338115767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 107833775447641827606568181 10109416448216421338115767)
  ·
    refine ⟨15164124672324632007173651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10109416448216421338115767 15164124672324632007173651)
    ·
      refine ⟨22746187008486948010760477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15164124672324632007173651 22746187008486948010760477)
      ·
        refine ⟨8529820128182605504035179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22746187008486948010760477 8529820128182605504035179)
        ·
          refine ⟨12794730192273908256052769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8529820128182605504035179 12794730192273908256052769)
          ·
            refine ⟨9596047644205431192039577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12794730192273908256052769 9596047644205431192039577)
            ·
              refine ⟨7197035733154073394029683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9596047644205431192039577 7197035733154073394029683)
              ·
                refine ⟨10795553599731110091044525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7197035733154073394029683 10795553599731110091044525)
                ·
                  refine ⟨4048332599899166284141697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10795553599731110091044525 4048332599899166284141697)
                  ·
                    refine ⟨3036249449924374713106273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4048332599899166284141697 3036249449924374713106273)
                    ·
                      refine ⟨2277187087443281034829705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3036249449924374713106273 2277187087443281034829705)
                      ·
                        rfl

theorem cell23_4434806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_4434806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4434806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4434806 prefixEnd_4434806 := by exact prefixLift 4434806
  have htrace : WordTrace (prefixWord ++ tailWord_4434806) baseStart_4434806 baseEnd_4434806 := by
    simpa [prefixWord, tailWord_4434806, baseEnd_4434806] using wordTrace_append hprefix tailTrace_4434806
  have hstable : (prefixWord ++ tailWord_4434806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4434806).length < 2 ^ (prefixWord ++ tailWord_4434806).sum := by decide
  have hdescent : baseEnd_4434806 < baseStart_4434806 := by decide
  rcases family_descends (prefixWord ++ tailWord_4434806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4434815 : List Nat := [1, 1, 2, 2, 1, 1, 4, 1, 5, 3, 2]
def baseStart_4434815 : Nat := 118140960795 + 4434815 * 2 ^ 59
def prefixEnd_4434815 : Nat := 4983230072969 + 3 ^ 40 * 4434815 * 2
def baseEnd_4434815 : Nat := 2277191708769171499617163

theorem tailTrace_4434815 : CollatzResearch.WordTrace tailWord_4434815 prefixEnd_4434815 2277191708769171499617163 := by
  unfold tailWord_4434815
  simp only [CollatzResearch.WordTrace]
  refine ⟨161750991428430135946929899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107833994285620090631286599 161750991428430135946929899)
  ·
    refine ⟨242626487142645203920394849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161750991428430135946929899 242626487142645203920394849)
    ·
      refine ⟨181969865356983902940296137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 242626487142645203920394849 181969865356983902940296137)
      ·
        refine ⟨136477399017737927205222103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181969865356983902940296137 136477399017737927205222103)
        ·
          refine ⟨204716098526606890807833155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136477399017737927205222103 204716098526606890807833155)
          ·
            refine ⟨307074147789910336211749733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204716098526606890807833155 307074147789910336211749733)
            ·
              refine ⟨57576402710608188039703075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 307074147789910336211749733 57576402710608188039703075)
              ·
                refine ⟨86364604065912282059554613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57576402710608188039703075 86364604065912282059554613)
                ·
                  refine ⟨8096681631179276443083245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 86364604065912282059554613 8096681631179276443083245)
                  ·
                    refine ⟨3036255611692228666156217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8096681631179276443083245 3036255611692228666156217)
                    ·
                      refine ⟨2277191708769171499617163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3036255611692228666156217 2277191708769171499617163)
                      ·
                        rfl

theorem cell23_4434815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 5, 3, 2].length) (baseStart_4434815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4434815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4434815 prefixEnd_4434815 := by exact prefixLift 4434815
  have htrace : WordTrace (prefixWord ++ tailWord_4434815) baseStart_4434815 baseEnd_4434815 := by
    simpa [prefixWord, tailWord_4434815, baseEnd_4434815] using wordTrace_append hprefix tailTrace_4434815
  have hstable : (prefixWord ++ tailWord_4434815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4434815).length < 2 ^ (prefixWord ++ tailWord_4434815).sum := by decide
  have hdescent : baseEnd_4434815 < baseStart_4434815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4434815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4434828 : List Nat := [2, 2, 1, 2, 1, 2, 2, 2, 2, 3, 4]
def baseStart_4434828 : Nat := 118140960795 + 4434828 * 2 ^ 59
def prefixEnd_4434828 : Nat := 4983230072969 + 3 ^ 40 * 4434828 * 2
def baseEnd_4434828 : Nat := 2277198384017679948754603

theorem tailTrace_4434828 : CollatzResearch.WordTrace tailWord_4434828 prefixEnd_4434828 2277198384017679948754603 := by
  unfold tailWord_4434828
  simp only [CollatzResearch.WordTrace]
  refine ⟨80875732788691519583576569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107834310384922026111435425 80875732788691519583576569)
  ·
    refine ⟨60656799591518639687682427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80875732788691519583576569 60656799591518639687682427)
    ·
      refine ⟨90985199387277959531523641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60656799591518639687682427 90985199387277959531523641)
      ·
        refine ⟨68238899540458469648642731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90985199387277959531523641 68238899540458469648642731)
        ·
          refine ⟨102358349310687704472964097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68238899540458469648642731 102358349310687704472964097)
          ·
            refine ⟨76768761983015778354723073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102358349310687704472964097 76768761983015778354723073)
            ·
              refine ⟨57576571487261833766042305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76768761983015778354723073 57576571487261833766042305)
              ·
                refine ⟨43182428615446375324531729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57576571487261833766042305 43182428615446375324531729)
                ·
                  refine ⟨32386821461584781493398797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43182428615446375324531729 32386821461584781493398797)
                  ·
                    refine ⟨12145058048094293060024549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32386821461584781493398797 12145058048094293060024549)
                    ·
                      refine ⟨2277198384017679948754603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12145058048094293060024549 2277198384017679948754603)
                      ·
                        rfl

theorem cell23_4434828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_4434828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4434828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4434828 prefixEnd_4434828 := by exact prefixLift 4434828
  have htrace : WordTrace (prefixWord ++ tailWord_4434828) baseStart_4434828 baseEnd_4434828 := by
    simpa [prefixWord, tailWord_4434828, baseEnd_4434828] using wordTrace_append hprefix tailTrace_4434828
  have hstable : (prefixWord ++ tailWord_4434828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4434828).length < 2 ^ (prefixWord ++ tailWord_4434828).sum := by decide
  have hdescent : baseEnd_4434828 < baseStart_4434828 := by decide
  rcases family_descends (prefixWord ++ tailWord_4434828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4434848 : List Nat := [2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 5]
def baseStart_4434848 : Nat := 118140960795 + 4434848 * 2 ^ 59
def prefixEnd_4434848 : Nat := 4983230072969 + 3 ^ 40 * 4434848 * 2
def baseEnd_4434848 : Nat := 2277208653630769870504511

theorem tailTrace_4434848 : CollatzResearch.WordTrace tailWord_4434848 prefixEnd_4434848 2277208653630769870504511 := by
  unfold tailWord_4434848
  simp only [CollatzResearch.WordTrace]
  refine ⟨80876097518655291291440599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107834796691540388388587465 80876097518655291291440599)
  ·
    refine ⟨121314146277982936937160899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80876097518655291291440599 121314146277982936937160899)
    ·
      refine ⟨181971219416974405405741349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121314146277982936937160899 181971219416974405405741349)
      ·
        refine ⟨34119603640682701013576503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 181971219416974405405741349 34119603640682701013576503)
        ·
          refine ⟨51179405461024051520364755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34119603640682701013576503 51179405461024051520364755)
          ·
            refine ⟨76769108191536077280547133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51179405461024051520364755 76769108191536077280547133)
            ·
              refine ⟨28788415571826028980205175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76769108191536077280547133 28788415571826028980205175)
              ·
                refine ⟨43182623357739043470307763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28788415571826028980205175 43182623357739043470307763)
                ·
                  refine ⟨64773935036608565205461645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43182623357739043470307763 64773935036608565205461645)
                  ·
                    refine ⟨24290225638728211952048117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 64773935036608565205461645 24290225638728211952048117)
                    ·
                      refine ⟨2277208653630769870504511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24290225638728211952048117 2277208653630769870504511)
                      ·
                        rfl

theorem cell23_4434848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_4434848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4434848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4434848 prefixEnd_4434848 := by exact prefixLift 4434848
  have htrace : WordTrace (prefixWord ++ tailWord_4434848) baseStart_4434848 baseEnd_4434848 := by
    simpa [prefixWord, tailWord_4434848, baseEnd_4434848] using wordTrace_append hprefix tailTrace_4434848
  have hstable : (prefixWord ++ tailWord_4434848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4434848).length < 2 ^ (prefixWord ++ tailWord_4434848).sum := by decide
  have hdescent : baseEnd_4434848 < baseStart_4434848 := by decide
  rcases family_descends (prefixWord ++ tailWord_4434848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4434849 : List Nat := [1, 2, 3, 4, 1, 1, 2, 3, 1, 3, 2]
def baseStart_4434849 : Nat := 118140960795 + 4434849 * 2 ^ 59
def prefixEnd_4434849 : Nat := 4983230072969 + 3 ^ 40 * 4434849 * 2
def baseEnd_4434849 : Nat := 2277209167111424366592007

theorem tailTrace_4434849 : CollatzResearch.WordTrace tailWord_4434849 prefixEnd_4434849 2277209167111424366592007 := by
  unfold tailWord_4434849
  simp only [CollatzResearch.WordTrace]
  refine ⟨161752231510306959753667601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107834821006871306502445067 161752231510306959753667601)
  ·
    refine ⟨121314173632730219815250701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161752231510306959753667601 121314173632730219815250701)
    ·
      refine ⟨45492815112273832430719013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121314173632730219815250701 45492815112273832430719013)
      ·
        refine ⟨8529902833551343580759815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45492815112273832430719013 8529902833551343580759815)
        ·
          refine ⟨12794854250327015371139723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8529902833551343580759815 12794854250327015371139723)
          ·
            refine ⟨19192281375490523056709585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12794854250327015371139723 19192281375490523056709585)
            ·
              refine ⟨14394211031617892292532189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19192281375490523056709585 14394211031617892292532189)
              ·
                refine ⟨5397829136856709609699571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14394211031617892292532189 5397829136856709609699571)
                ·
                  refine ⟨8096743705285064414549357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5397829136856709609699571 8096743705285064414549357)
                  ·
                    refine ⟨3036278889481899155456009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8096743705285064414549357 3036278889481899155456009)
                    ·
                      refine ⟨2277209167111424366592007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3036278889481899155456009 2277209167111424366592007)
                      ·
                        rfl

theorem cell23_4434849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_4434849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4434849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4434849 prefixEnd_4434849 := by exact prefixLift 4434849
  have htrace : WordTrace (prefixWord ++ tailWord_4434849) baseStart_4434849 baseEnd_4434849 := by
    simpa [prefixWord, tailWord_4434849, baseEnd_4434849] using wordTrace_append hprefix tailTrace_4434849
  have hstable : (prefixWord ++ tailWord_4434849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4434849).length < 2 ^ (prefixWord ++ tailWord_4434849).sum := by decide
  have hdescent : baseEnd_4434849 < baseStart_4434849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4434849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4434915 : List Nat := [1, 1, 1, 6, 1, 1, 1, 4, 2, 5]
def baseStart_4434915 : Nat := 118140960795 + 4434915 * 2 ^ 59
def prefixEnd_4434915 : Nat := 4983230072969 + 3 ^ 40 * 4434915 * 2
def baseEnd_4434915 : Nat := 759081018944873702788901

theorem tailTrace_4434915 : CollatzResearch.WordTrace tailWord_4434915 prefixEnd_4434915 759081018944873702788901 := by
  unfold tailWord_4434915
  simp only [CollatzResearch.WordTrace]
  refine ⟨161754638728067853025570199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107836425818711902017046799 161754638728067853025570199)
  ·
    refine ⟨242631958092101779538355299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161754638728067853025570199 242631958092101779538355299)
    ·
      refine ⟨363947937138152669307532949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242631958092101779538355299 363947937138152669307532949)
      ·
        refine ⟨17060059553350906373790607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 363947937138152669307532949 17060059553350906373790607)
        ·
          refine ⟨25590089330026359560685911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17060059553350906373790607 25590089330026359560685911)
          ·
            refine ⟨38385133995039539341028867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25590089330026359560685911 38385133995039539341028867)
            ·
              refine ⟨57577700992559309011543301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38385133995039539341028867 57577700992559309011543301)
              ·
                refine ⟨10795818936104870439664369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57577700992559309011543301 10795818936104870439664369)
                ·
                  refine ⟨8096864202078652829748277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10795818936104870439664369 8096864202078652829748277)
                  ·
                    refine ⟨759081018944873702788901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8096864202078652829748277 759081018944873702788901)
                    ·
                      rfl

theorem cell23_4434915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 4, 2, 5].length) (baseStart_4434915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4434915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4434915 prefixEnd_4434915 := by exact prefixLift 4434915
  have htrace : WordTrace (prefixWord ++ tailWord_4434915) baseStart_4434915 baseEnd_4434915 := by
    simpa [prefixWord, tailWord_4434915, baseEnd_4434915] using wordTrace_append hprefix tailTrace_4434915
  have hstable : (prefixWord ++ tailWord_4434915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4434915).length < 2 ^ (prefixWord ++ tailWord_4434915).sum := by decide
  have hdescent : baseEnd_4434915 < baseStart_4434915 := by decide
  rcases family_descends (prefixWord ++ tailWord_4434915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4434919 : List Nat := [1, 1, 5, 2, 2, 1, 4, 2, 5]
def baseStart_4434919 : Nat := 118140960795 + 4434919 * 2 ^ 59
def prefixEnd_4434919 : Nat := 4983230072969 + 3 ^ 40 * 4434919 * 2
def baseEnd_4434919 : Nat := 253027234528582121412965

theorem tailTrace_4434919 : CollatzResearch.WordTrace tailWord_4434919 prefixEnd_4434919 253027234528582121412965 := by
  unfold tailWord_4434919
  simp only [CollatzResearch.WordTrace]
  refine ⟨161754784620053361708715811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107836523080035574472477207 161754784620053361708715811)
  ·
    refine ⟨242632176930080042563073717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161754784620053361708715811 242632176930080042563073717)
    ·
      refine ⟨22746766587195003990288161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 242632176930080042563073717 22746766587195003990288161)
      ·
        refine ⟨17060074940396252992716121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22746766587195003990288161 17060074940396252992716121)
        ·
          refine ⟨12795056205297189744537091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17060074940396252992716121 12795056205297189744537091)
          ·
            refine ⟨19192584307945784616805637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12795056205297189744537091 19192584307945784616805637)
            ·
              refine ⟨3598609557739834615651057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19192584307945784616805637 3598609557739834615651057)
              ·
                refine ⟨2698957168304875961738293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3598609557739834615651057 2698957168304875961738293)
                ·
                  refine ⟨253027234528582121412965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2698957168304875961738293 253027234528582121412965)
                  ·
                    rfl

theorem cell23_4434919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4, 2, 5].length) (baseStart_4434919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4434919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4434919 prefixEnd_4434919 := by exact prefixLift 4434919
  have htrace : WordTrace (prefixWord ++ tailWord_4434919) baseStart_4434919 baseEnd_4434919 := by
    simpa [prefixWord, tailWord_4434919, baseEnd_4434919] using wordTrace_append hprefix tailTrace_4434919
  have hstable : (prefixWord ++ tailWord_4434919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4434919).length < 2 ^ (prefixWord ++ tailWord_4434919).sum := by decide
  have hdescent : baseEnd_4434919 < baseStart_4434919 := by decide
  rcases family_descends (prefixWord ++ tailWord_4434919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4434922 : List Nat := [3, 1, 3, 1, 2, 2, 1, 1, 2, 5, 2]
def baseStart_4434922 : Nat := 118140960795 + 4434922 * 2 ^ 59
def prefixEnd_4434922 : Nat := 4983230072969 + 3 ^ 40 * 4434922 * 2
def baseEnd_4434922 : Nat := 2277246651199202580979171

theorem tailTrace_4434922 : CollatzResearch.WordTrace tailWord_4434922 prefixEnd_4434922 2277246651199202580979171 := by
  unfold tailWord_4434922
  simp only [CollatzResearch.WordTrace]
  refine ⟨40438723509760623305268755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107836596026028328814050013 40438723509760623305268755)
  ·
    refine ⟨60658085264640934957903133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40438723509760623305268755 60658085264640934957903133)
    ·
      refine ⟨22746781974240350609213675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60658085264640934957903133 22746781974240350609213675)
      ·
        refine ⟨34120172961360525913820513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22746781974240350609213675 34120172961360525913820513)
        ·
          refine ⟨25590129721020394435365385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34120172961360525913820513 25590129721020394435365385)
          ·
            refine ⟨19192597290765295826524039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25590129721020394435365385 19192597290765295826524039)
            ·
              refine ⟨28788895936147943739786059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19192597290765295826524039 28788895936147943739786059)
              ·
                refine ⟨43183343904221915609679089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28788895936147943739786059 43183343904221915609679089)
                ·
                  refine ⟨32387507928166436707259317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43183343904221915609679089 32387507928166436707259317)
                  ·
                    refine ⟨3036328868265603441305561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32387507928166436707259317 3036328868265603441305561)
                    ·
                      refine ⟨2277246651199202580979171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3036328868265603441305561 2277246651199202580979171)
                      ·
                        rfl

theorem cell23_4434922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 2, 5, 2].length) (baseStart_4434922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4434922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4434922 prefixEnd_4434922 := by exact prefixLift 4434922
  have htrace : WordTrace (prefixWord ++ tailWord_4434922) baseStart_4434922 baseEnd_4434922 := by
    simpa [prefixWord, tailWord_4434922, baseEnd_4434922] using wordTrace_append hprefix tailTrace_4434922
  have hstable : (prefixWord ++ tailWord_4434922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4434922).length < 2 ^ (prefixWord ++ tailWord_4434922).sum := by decide
  have hdescent : baseEnd_4434922 < baseStart_4434922 := by decide
  rcases family_descends (prefixWord ++ tailWord_4434922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4434928 : List Nat := [2, 1, 1, 1, 3, 2, 1, 2, 2, 8]
def baseStart_4434928 : Nat := 118140960795 + 4434928 * 2 ^ 59
def prefixEnd_4434928 : Nat := 4983230072969 + 3 ^ 40 * 4434928 * 2
def baseEnd_4434928 : Nat := 759083244027709852501381

theorem tailTrace_4434928 : CollatzResearch.WordTrace tailWord_4434928 prefixEnd_4434928 759083244027709852501381 := by
  unfold tailWord_4434928
  simp only [CollatzResearch.WordTrace]
  refine ⟨80877556438510378122896719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107836741918013837497195625 80877556438510378122896719)
  ·
    refine ⟨121316334657765567184345079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80877556438510378122896719 121316334657765567184345079)
    ·
      refine ⟨181974501986648350776517619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121316334657765567184345079 181974501986648350776517619)
      ·
        refine ⟨272961752979972526164776429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181974501986648350776517619 272961752979972526164776429)
        ·
          refine ⟨102360657367489697311791161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 272961752979972526164776429 102360657367489697311791161)
          ·
            refine ⟨76770493025617272983843371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102360657367489697311791161 76770493025617272983843371)
            ·
              refine ⟨115155739538425909475765057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76770493025617272983843371 115155739538425909475765057)
              ·
                refine ⟨86366804653819432106823793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115155739538425909475765057 86366804653819432106823793)
                ·
                  refine ⟨64775103490364574080117845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86366804653819432106823793 64775103490364574080117845)
                  ·
                    refine ⟨759083244027709852501381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 64775103490364574080117845 759083244027709852501381)
                    ·
                      rfl

theorem cell23_4434928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 2, 8].length) (baseStart_4434928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4434928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4434928 prefixEnd_4434928 := by exact prefixLift 4434928
  have htrace : WordTrace (prefixWord ++ tailWord_4434928) baseStart_4434928 baseEnd_4434928 := by
    simpa [prefixWord, tailWord_4434928, baseEnd_4434928] using wordTrace_append hprefix tailTrace_4434928
  have hstable : (prefixWord ++ tailWord_4434928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4434928).length < 2 ^ (prefixWord ++ tailWord_4434928).sum := by decide
  have hdescent : baseEnd_4434928 < baseStart_4434928 := by decide
  rcases family_descends (prefixWord ++ tailWord_4434928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4434952 : List Nat := [2, 1, 3, 2, 1, 3, 3, 1, 2, 1, 4]
def baseStart_4434952 : Nat := 118140960795 + 4434952 * 2 ^ 59
def prefixEnd_4434952 : Nat := 4983230072969 + 3 ^ 40 * 4434952 * 2
def baseEnd_4434952 : Nat := 2277262055618837463604033

theorem tailTrace_4434952 : CollatzResearch.WordTrace tailWord_4434952 prefixEnd_4434952 2277262055618837463604033 := by
  unfold tailWord_4434952
  simp only [CollatzResearch.WordTrace]
  refine ⟨80877994114466904172333555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107837325485955872229778073 80877994114466904172333555)
  ·
    refine ⟨121316991171700356258500333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80877994114466904172333555 121316991171700356258500333)
    ·
      refine ⟨45493871689387633596937625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121316991171700356258500333 45493871689387633596937625)
      ·
        refine ⟨34120403767040725197703219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45493871689387633596937625 34120403767040725197703219)
        ·
          refine ⟨51180605650561087796554829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34120403767040725197703219 51180605650561087796554829)
          ·
            refine ⟨19192727118960407923708061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51180605650561087796554829 19192727118960407923708061)
            ·
              refine ⟨7197272669610152971390523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19192727118960407923708061 7197272669610152971390523)
              ·
                refine ⟨10795909004415229457085785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7197272669610152971390523 10795909004415229457085785)
                ·
                  refine ⟨8096931753311422092814339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10795909004415229457085785 8096931753311422092814339)
                  ·
                    refine ⟨12145397629967133139221509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8096931753311422092814339 12145397629967133139221509)
                    ·
                      refine ⟨2277262055618837463604033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12145397629967133139221509 2277262055618837463604033)
                      ·
                        rfl

theorem cell23_4434952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_4434952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4434952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4434952 prefixEnd_4434952 := by exact prefixLift 4434952
  have htrace : WordTrace (prefixWord ++ tailWord_4434952) baseStart_4434952 baseEnd_4434952 := by
    simpa [prefixWord, tailWord_4434952, baseEnd_4434952] using wordTrace_append hprefix tailTrace_4434952
  have hstable : (prefixWord ++ tailWord_4434952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4434952).length < 2 ^ (prefixWord ++ tailWord_4434952).sum := by decide
  have hdescent : baseEnd_4434952 < baseStart_4434952 := by decide
  rcases family_descends (prefixWord ++ tailWord_4434952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4434965 : List Nat := [1, 3, 2, 1, 4, 1, 1, 1, 2, 1, 6]
def baseStart_4434965 : Nat := 118140960795 + 4434965 * 2 ^ 59
def prefixEnd_4434965 : Nat := 4983230072969 + 3 ^ 40 * 4434965 * 2
def baseEnd_4434965 : Nat := 2277268730867345912741473

theorem tailTrace_4434965 : CollatzResearch.WordTrace tailWord_4434965 prefixEnd_4434965 2277268730867345912741473 := by
  unfold tailWord_4434965
  simp only [CollatzResearch.WordTrace]
  refine ⟨161756462377886711564890349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107837641585257807709926899 161756462377886711564890349)
  ·
    refine ⟨60658673391707516836833881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161756462377886711564890349 60658673391707516836833881)
    ·
      refine ⟨45494005043780637627625411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60658673391707516836833881 45494005043780637627625411)
      ·
        refine ⟨68241007565670956441438117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45494005043780637627625411 68241007565670956441438117)
        ·
          refine ⟨12795188918563304332769647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68241007565670956441438117 12795188918563304332769647)
          ·
            refine ⟨19192783377844956499154471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12795188918563304332769647 19192783377844956499154471)
            ·
              refine ⟨28789175066767434748731707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19192783377844956499154471 28789175066767434748731707)
              ·
                refine ⟨43183762600151152123097561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28789175066767434748731707 43183762600151152123097561)
                ·
                  refine ⟨32387821950113364092323171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43183762600151152123097561 32387821950113364092323171)
                  ·
                    refine ⟨48581732925170046138484757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32387821950113364092323171 48581732925170046138484757)
                    ·
                      refine ⟨2277268730867345912741473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48581732925170046138484757 2277268730867345912741473)
                      ·
                        rfl

theorem cell23_4434965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_4434965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4434965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4434965 prefixEnd_4434965 := by exact prefixLift 4434965
  have htrace : WordTrace (prefixWord ++ tailWord_4434965) baseStart_4434965 baseEnd_4434965 := by
    simpa [prefixWord, tailWord_4434965, baseEnd_4434965] using wordTrace_append hprefix tailTrace_4434965
  have hstable : (prefixWord ++ tailWord_4434965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4434965).length < 2 ^ (prefixWord ++ tailWord_4434965).sum := by decide
  have hdescent : baseEnd_4434965 < baseStart_4434965 := by decide
  rcases family_descends (prefixWord ++ tailWord_4434965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4434975 : List Nat := [1, 1, 2, 4, 1, 4, 1, 1, 8]
def baseStart_4434975 : Nat := 118140960795 + 4434975 * 2 ^ 59
def prefixEnd_4434975 : Nat := 4983230072969 + 3 ^ 40 * 4434975 * 2
def baseEnd_4434975 : Nat := 253030429519321208179603

theorem tailTrace_4434975 : CollatzResearch.WordTrace tailWord_4434975 prefixEnd_4434975 253030429519321208179603 := by
  unfold tailWord_4434975
  simp only [CollatzResearch.WordTrace]
  refine ⟨161756827107850483272754379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107837884738566988848502919 161756827107850483272754379)
  ·
    refine ⟨242635240661775724909131569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161756827107850483272754379 242635240661775724909131569)
    ·
      refine ⟨181976430496331793681848677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 242635240661775724909131569 181976430496331793681848677)
      ·
        refine ⟨34120580718062211315346627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 181976430496331793681848677 34120580718062211315346627)
        ·
          refine ⟨51180871077093316973019941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34120580718062211315346627 51180871077093316973019941)
          ·
            refine ⟨9596413326954996932441239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51180871077093316973019941 9596413326954996932441239)
            ·
              refine ⟨14394619990432495398661859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9596413326954996932441239 14394619990432495398661859)
              ·
                refine ⟨21591929985648743097992789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14394619990432495398661859 21591929985648743097992789)
                ·
                  refine ⟨253030429519321208179603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21591929985648743097992789 253030429519321208179603)
                  ·
                    rfl

theorem cell23_4434975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 8].length) (baseStart_4434975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4434975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4434975 prefixEnd_4434975 := by exact prefixLift 4434975
  have htrace : WordTrace (prefixWord ++ tailWord_4434975) baseStart_4434975 baseEnd_4434975 := by
    simpa [prefixWord, tailWord_4434975, baseEnd_4434975] using wordTrace_append hprefix tailTrace_4434975
  have hstable : (prefixWord ++ tailWord_4434975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4434975).length < 2 ^ (prefixWord ++ tailWord_4434975).sum := by decide
  have hdescent : baseEnd_4434975 < baseStart_4434975 := by decide
  rcases family_descends (prefixWord ++ tailWord_4434975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4434979 : List Nat := [1, 1, 1, 4, 3, 2, 2, 4, 1, 4]
def baseStart_4434979 : Nat := 118140960795 + 4434979 * 2 ^ 59
def prefixEnd_4434979 : Nat := 4983230072969 + 3 ^ 40 * 4434979 * 2
def baseEnd_4434979 : Nat := 759091973198836285988803

theorem tailTrace_4434979 : CollatzResearch.WordTrace tailWord_4434979 prefixEnd_4434979 759091973198836285988803 := by
  unfold tailWord_4434979
  simp only [CollatzResearch.WordTrace]
  refine ⟨161756972999835991955899991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107837981999890661303933327 161756972999835991955899991)
  ·
    refine ⟨242635459499753987933849987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161756972999835991955899991 242635459499753987933849987)
    ·
      refine ⟨363953189249630981900774981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242635459499753987933849987 363953189249630981900774981)
      ·
        refine ⟨68241222984305809106395309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 363953189249630981900774981 68241222984305809106395309)
        ·
          refine ⟨25590458619114678414898241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68241222984305809106395309 25590458619114678414898241)
          ·
            refine ⟨19192843964336008811173681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25590458619114678414898241 19192843964336008811173681)
            ·
              refine ⟨14394632973252006608380261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19192843964336008811173681 14394632973252006608380261)
              ·
                refine ⟨2698993682484751239071299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14394632973252006608380261 2698993682484751239071299)
                ·
                  refine ⟨4048490523727126858606949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2698993682484751239071299 4048490523727126858606949)
                  ·
                    refine ⟨759091973198836285988803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4048490523727126858606949 759091973198836285988803)
                    ·
                      rfl

theorem cell23_4434979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 4, 1, 4].length) (baseStart_4434979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4434979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4434979 prefixEnd_4434979 := by exact prefixLift 4434979
  have htrace : WordTrace (prefixWord ++ tailWord_4434979) baseStart_4434979 baseEnd_4434979 := by
    simpa [prefixWord, tailWord_4434979, baseEnd_4434979] using wordTrace_append hprefix tailTrace_4434979
  have hstable : (prefixWord ++ tailWord_4434979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4434979).length < 2 ^ (prefixWord ++ tailWord_4434979).sum := by decide
  have hdescent : baseEnd_4434979 < baseStart_4434979 := by decide
  rcases family_descends (prefixWord ++ tailWord_4434979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4434992 : List Nat := [2, 1, 1, 1, 2, 4, 5, 1, 6]
def baseStart_4434992 : Nat := 118140960795 + 4434992 * 2 ^ 59
def prefixEnd_4434992 : Nat := 4983230072969 + 3 ^ 40 * 4434992 * 2
def baseEnd_4434992 : Nat := 253031399427224145233761

theorem tailTrace_4434992 : CollatzResearch.WordTrace tailWord_4434992 prefixEnd_4434992 253031399427224145233761 := by
  unfold tailWord_4434992
  simp only [CollatzResearch.WordTrace]
  refine ⟨80878723574394447588061615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107838298099192596784082153 80878723574394447588061615)
  ·
    refine ⟨121318085361591671382092423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80878723574394447588061615 121318085361591671382092423)
    ·
      refine ⟨181977128042387507073138635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121318085361591671382092423 181977128042387507073138635)
      ·
        refine ⟨272965692063581260609707953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181977128042387507073138635 272965692063581260609707953)
        ·
          refine ⟨204724269047685945457280965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 272965692063581260609707953 204724269047685945457280965)
          ·
            refine ⟨38385800446441114773240181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 204724269047685945457280965 38385800446441114773240181)
            ·
              refine ⟨3598668791853854509991267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38385800446441114773240181 3598668791853854509991267)
              ·
                refine ⟨5398003187780781764986901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3598668791853854509991267 5398003187780781764986901)
                ·
                  refine ⟨253031399427224145233761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5398003187780781764986901 253031399427224145233761)
                  ·
                    rfl

theorem cell23_4434992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5, 1, 6].length) (baseStart_4434992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4434992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4434992 prefixEnd_4434992 := by exact prefixLift 4434992
  have htrace : WordTrace (prefixWord ++ tailWord_4434992) baseStart_4434992 baseEnd_4434992 := by
    simpa [prefixWord, tailWord_4434992, baseEnd_4434992] using wordTrace_append hprefix tailTrace_4434992
  have hstable : (prefixWord ++ tailWord_4434992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4434992).length < 2 ^ (prefixWord ++ tailWord_4434992).sum := by decide
  have hdescent : baseEnd_4434992 < baseStart_4434992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4434992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4435022 : List Nat := [4, 1, 1, 1, 1, 3, 1, 5, 1, 5]
def baseStart_4435022 : Nat := 118140960795 + 4435022 * 2 ^ 59
def prefixEnd_4435022 : Nat := 4983230072969 + 3 ^ 40 * 4435022 * 2
def baseEnd_4435022 : Nat := 759099333088217396576237

theorem tailTrace_4435022 : CollatzResearch.WordTrace tailWord_4435022 prefixEnd_4435022 759099333088217396576237 := by
  unfold tailWord_4435022
  simp only [CollatzResearch.WordTrace]
  refine ⟨20219817667335026287464415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107839027559120140199810213 20219817667335026287464415)
  ·
    refine ⟨30329726501002539431196623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20219817667335026287464415 30329726501002539431196623)
    ·
      refine ⟨45494589751503809146794935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30329726501002539431196623 45494589751503809146794935)
      ·
        refine ⟨68241884627255713720192403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45494589751503809146794935 68241884627255713720192403)
        ·
          refine ⟨102362826940883570580288605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68241884627255713720192403 102362826940883570580288605)
          ·
            refine ⟨38386060102831338967608227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102362826940883570580288605 38386060102831338967608227)
            ·
              refine ⟨57579090154247008451412341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38386060102831338967608227 57579090154247008451412341)
              ·
                refine ⟨5398039701960657042319907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57579090154247008451412341 5398039701960657042319907)
                ·
                  refine ⟨8097059552940985563479861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5398039701960657042319907 8097059552940985563479861)
                  ·
                    refine ⟨759099333088217396576237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8097059552940985563479861 759099333088217396576237)
                    ·
                      rfl

theorem cell23_4435022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 5, 1, 5].length) (baseStart_4435022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4435022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4435022 prefixEnd_4435022 := by exact prefixLift 4435022
  have htrace : WordTrace (prefixWord ++ tailWord_4435022) baseStart_4435022 baseEnd_4435022 := by
    simpa [prefixWord, tailWord_4435022, baseEnd_4435022] using wordTrace_append hprefix tailTrace_4435022
  have hstable : (prefixWord ++ tailWord_4435022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4435022).length < 2 ^ (prefixWord ++ tailWord_4435022).sum := by decide
  have hdescent : baseEnd_4435022 < baseStart_4435022 := by decide
  rcases family_descends (prefixWord ++ tailWord_4435022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4435029 : List Nat := [1, 3, 2, 2, 1, 2, 3, 2, 2, 3, 2]
def baseStart_4435029 : Nat := 118140960795 + 4435029 * 2 ^ 59
def prefixEnd_4435029 : Nat := 4983230072969 + 3 ^ 40 * 4435029 * 2
def baseEnd_4435029 : Nat := 2277301593629233662341179

theorem tailTrace_4435029 : CollatzResearch.WordTrace tailWord_4435029 prefixEnd_4435029 2277301593629233662341179 := by
  unfold tailWord_4435029
  simp only [CollatzResearch.WordTrace]
  refine ⟨161758796649654850495220141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107839197766436566996813427 161758796649654850495220141)
  ·
    refine ⟨60659548743620568935707553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161758796649654850495220141 60659548743620568935707553)
    ·
      refine ⟨45494661557715426701780665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60659548743620568935707553 45494661557715426701780665)
      ·
        refine ⟨34120996168286570026335499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45494661557715426701780665 34120996168286570026335499)
        ·
          refine ⟨51181494252429855039503249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34120996168286570026335499 51181494252429855039503249)
          ·
            refine ⟨38386120689322391279627437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51181494252429855039503249 38386120689322391279627437)
            ·
              refine ⟨14394795258495896729860289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38386120689322391279627437 14394795258495896729860289)
              ·
                refine ⟨10796096443871922547395217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14394795258495896729860289 10796096443871922547395217)
                ·
                  refine ⟨8097072332903941910546413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10796096443871922547395217 8097072332903941910546413)
                  ·
                    refine ⟨3036402124838978216454905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8097072332903941910546413 3036402124838978216454905)
                    ·
                      refine ⟨2277301593629233662341179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3036402124838978216454905 2277301593629233662341179)
                      ·
                        rfl

theorem cell23_4435029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 2, 2, 3, 2].length) (baseStart_4435029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4435029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4435029 prefixEnd_4435029 := by exact prefixLift 4435029
  have htrace : WordTrace (prefixWord ++ tailWord_4435029) baseStart_4435029 baseEnd_4435029 := by
    simpa [prefixWord, tailWord_4435029, baseEnd_4435029] using wordTrace_append hprefix tailTrace_4435029
  have hstable : (prefixWord ++ tailWord_4435029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4435029).length < 2 ^ (prefixWord ++ tailWord_4435029).sum := by decide
  have hdescent : baseEnd_4435029 < baseStart_4435029 := by decide
  rcases family_descends (prefixWord ++ tailWord_4435029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4435030 : List Nat := [5, 2, 2, 1, 3, 1, 1, 1, 3, 4]
def baseStart_4435030 : Nat := 118140960795 + 4435030 * 2 ^ 59
def prefixEnd_4435030 : Nat := 4983230072969 + 3 ^ 40 * 4435030 * 2
def baseEnd_4435030 : Nat := 759100702369962719476225

theorem tailTrace_4435030 : CollatzResearch.WordTrace tailWord_4435030 prefixEnd_4435030 759100702369962719476225 := by
  unfold tailWord_4435030
  simp only [CollatzResearch.WordTrace]
  refine ⟨10109927070165701729125409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 107839222081767485110671029 10109927070165701729125409)
  ·
    refine ⟨7582445302624276296844057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10109927070165701729125409 7582445302624276296844057)
    ·
      refine ⟨5686833976968207222633043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7582445302624276296844057 5686833976968207222633043)
      ·
        refine ⟨8530250965452310833949565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5686833976968207222633043 8530250965452310833949565)
        ·
          refine ⟨3198844112044616562731087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8530250965452310833949565 3198844112044616562731087)
          ·
            refine ⟨4798266168066924844096631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3198844112044616562731087 4798266168066924844096631)
            ·
              refine ⟨7197399252100387266144947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4798266168066924844096631 7197399252100387266144947)
              ·
                refine ⟨10796098878150580899217421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7197399252100387266144947 10796098878150580899217421)
                ·
                  refine ⟨4048537079306467837206533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10796098878150580899217421 4048537079306467837206533)
                  ·
                    refine ⟨759100702369962719476225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4048537079306467837206533 759100702369962719476225)
                    ·
                      rfl

theorem cell23_4435030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_4435030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4435030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4435030 prefixEnd_4435030 := by exact prefixLift 4435030
  have htrace : WordTrace (prefixWord ++ tailWord_4435030) baseStart_4435030 baseEnd_4435030 := by
    simpa [prefixWord, tailWord_4435030, baseEnd_4435030] using wordTrace_append hprefix tailTrace_4435030
  have hstable : (prefixWord ++ tailWord_4435030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4435030).length < 2 ^ (prefixWord ++ tailWord_4435030).sum := by decide
  have hdescent : baseEnd_4435030 < baseStart_4435030 := by decide
  rcases family_descends (prefixWord ++ tailWord_4435030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4435055 : List Nat := [1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 6]
def baseStart_4435055 : Nat := 118140960795 + 4435055 * 2 ^ 59
def prefixEnd_4435055 : Nat := 4983230072969 + 3 ^ 40 * 4435055 * 2
def baseEnd_4435055 : Nat := 2277314944126250560616059

theorem tailTrace_4435055 : CollatzResearch.WordTrace tailWord_4435055 prefixEnd_4435055 2277314944126250560616059 := by
  unfold tailWord_4435055
  simp only [CollatzResearch.WordTrace]
  refine ⟨161759744947560656935666619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107839829965040437957111079 161759744947560656935666619)
  ·
    refine ⟨242639617421340985403499929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161759744947560656935666619 242639617421340985403499929)
    ·
      refine ⟨181979713066005739052624947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 242639617421340985403499929 181979713066005739052624947)
      ·
        refine ⟨272969569599008608578937421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181979713066005739052624947 272969569599008608578937421)
        ·
          refine ⟨102363588599628228217101533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 272969569599008608578937421 102363588599628228217101533)
          ·
            refine ⟨38386345724860585581413075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102363588599628228217101533 38386345724860585581413075)
            ·
              refine ⟨57579518587290878372119613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38386345724860585581413075 57579518587290878372119613)
              ·
                refine ⟨21592319470234079389544855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57579518587290878372119613 21592319470234079389544855)
                ·
                  refine ⟨32388479205351119084317283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21592319470234079389544855 32388479205351119084317283)
                  ·
                    refine ⟨48582718808026678626475925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32388479205351119084317283 48582718808026678626475925)
                    ·
                      refine ⟨2277314944126250560616059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48582718808026678626475925 2277314944126250560616059)
                      ·
                        rfl

theorem cell23_4435055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 6].length) (baseStart_4435055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4435055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4435055 prefixEnd_4435055 := by exact prefixLift 4435055
  have htrace : WordTrace (prefixWord ++ tailWord_4435055) baseStart_4435055 baseEnd_4435055 := by
    simpa [prefixWord, tailWord_4435055, baseEnd_4435055] using wordTrace_append hprefix tailTrace_4435055
  have hstable : (prefixWord ++ tailWord_4435055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4435055).length < 2 ^ (prefixWord ++ tailWord_4435055).sum := by decide
  have hdescent : baseEnd_4435055 < baseStart_4435055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4435055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4435076 : List Nat := [2, 3, 2, 1, 2, 3, 3, 1, 1, 1, 4]
def baseStart_4435076 : Nat := 118140960795 + 4435076 * 2 ^ 59
def prefixEnd_4435076 : Nat := 4983230072969 + 3 ^ 40 * 4435076 * 2
def baseEnd_4435076 : Nat := 2277325727219994978453463

theorem tailTrace_4435076 : CollatzResearch.WordTrace tailWord_4435076 prefixEnd_4435076 2277325727219994978453463 := by
  unfold tailWord_4435076
  simp only [CollatzResearch.WordTrace]
  refine ⟨80880255440242288761090541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107840340586989718348120721 80880255440242288761090541)
  ·
    refine ⟨30330095790090858285408953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80880255440242288761090541 30330095790090858285408953)
    ·
      refine ⟨22747571842568143714056715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30330095790090858285408953 22747571842568143714056715)
      ·
        refine ⟨34121357763852215571085073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22747571842568143714056715 34121357763852215571085073)
        ·
          refine ⟨25591018322889161678313805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34121357763852215571085073 25591018322889161678313805)
          ·
            refine ⟨9596631871083435629367677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25591018322889161678313805 9596631871083435629367677)
            ·
              refine ⟨3598736951656288361012879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9596631871083435629367677 3598736951656288361012879)
              ·
                refine ⟨5398105427484432541519319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3598736951656288361012879 5398105427484432541519319)
                ·
                  refine ⟨8097158141226648812278979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5398105427484432541519319 8097158141226648812278979)
                  ·
                    refine ⟨12145737211839973218418469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8097158141226648812278979 12145737211839973218418469)
                    ·
                      refine ⟨2277325727219994978453463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12145737211839973218418469 2277325727219994978453463)
                      ·
                        rfl

theorem cell23_4435076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3, 1, 1, 1, 4].length) (baseStart_4435076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4435076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4435076 prefixEnd_4435076 := by exact prefixLift 4435076
  have htrace : WordTrace (prefixWord ++ tailWord_4435076) baseStart_4435076 baseEnd_4435076 := by
    simpa [prefixWord, tailWord_4435076, baseEnd_4435076] using wordTrace_append hprefix tailTrace_4435076
  have hstable : (prefixWord ++ tailWord_4435076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4435076).length < 2 ^ (prefixWord ++ tailWord_4435076).sum := by decide
  have hdescent : baseEnd_4435076 < baseStart_4435076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4435076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4435086 : List Nat := [4, 1, 1, 3, 2, 2, 2, 2, 2, 4]
def baseStart_4435086 : Nat := 118140960795 + 4435086 * 2 ^ 59
def prefixEnd_4435086 : Nat := 4983230072969 + 3 ^ 40 * 4435086 * 2
def baseEnd_4435086 : Nat := 759110287342179979776139

theorem tailTrace_4435086 : CollatzResearch.WordTrace tailWord_4435086 prefixEnd_4435086 759110287342179979776139 := by
  unfold tailWord_4435086
  simp only [CollatzResearch.WordTrace]
  refine ⟨20220109451306043653755639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107840583740298899486696741 20220109451306043653755639)
  ·
    refine ⟨30330164176959065480633459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20220109451306043653755639 30330164176959065480633459)
    ·
      refine ⟨45495246265438598220950189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30330164176959065480633459 45495246265438598220950189)
      ·
        refine ⟨17060717349539474332856321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45495246265438598220950189 17060717349539474332856321)
        ·
          refine ⟨12795538012154605749642241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17060717349539474332856321 12795538012154605749642241)
          ·
            refine ⟨9596653509115954312231681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12795538012154605749642241 9596653509115954312231681)
            ·
              refine ⟨7197490131836965734173761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9596653509115954312231681 7197490131836965734173761)
              ·
                refine ⟨5398117598877724300630321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7197490131836965734173761 5398117598877724300630321)
                ·
                  refine ⟨4048588199158293225472741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5398117598877724300630321 4048588199158293225472741)
                  ·
                    refine ⟨759110287342179979776139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4048588199158293225472741 759110287342179979776139)
                    ·
                      rfl

theorem cell23_4435086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 2, 2, 4].length) (baseStart_4435086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4435086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4435086 prefixEnd_4435086 := by exact prefixLift 4435086
  have htrace : WordTrace (prefixWord ++ tailWord_4435086) baseStart_4435086 baseEnd_4435086 := by
    simpa [prefixWord, tailWord_4435086, baseEnd_4435086] using wordTrace_append hprefix tailTrace_4435086
  have hstable : (prefixWord ++ tailWord_4435086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4435086).length < 2 ^ (prefixWord ++ tailWord_4435086).sum := by decide
  have hdescent : baseEnd_4435086 < baseStart_4435086 := by decide
  rcases family_descends (prefixWord ++ tailWord_4435086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4435106 : List Nat := [3, 3, 1, 3, 2, 1, 2, 1, 1, 2, 4]
def baseStart_4435106 : Nat := 118140960795 + 4435106 * 2 ^ 59
def prefixEnd_4435106 : Nat := 4983230072969 + 3 ^ 40 * 4435106 * 2
def baseEnd_4435106 : Nat := 2277341131639629861078325

theorem tailTrace_4435106 : CollatzResearch.WordTrace tailWord_4435106 prefixEnd_4435106 2277341131639629861078325 := by
  unfold tailWord_4435106
  simp only [CollatzResearch.WordTrace]
  refine ⟨40440401267593973161443293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107841070046917261763848781 40440401267593973161443293)
  ·
    refine ⟨15165150475347739935541235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40440401267593973161443293 15165150475347739935541235)
    ·
      refine ⟨22747725713021609903311853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15165150475347739935541235 22747725713021609903311853)
      ·
        refine ⟨8530397142383103713741945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22747725713021609903311853 8530397142383103713741945)
        ·
          refine ⟨6397797856787327785306459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8530397142383103713741945 6397797856787327785306459)
          ·
            refine ⟨9596696785180991677959689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6397797856787327785306459 9596696785180991677959689)
            ·
              refine ⟨7197522588885743758469767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9596696785180991677959689 7197522588885743758469767)
              ·
                refine ⟨10796283883328615637704651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7197522588885743758469767 10796283883328615637704651)
                ·
                  refine ⟨16194425824992923456556977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10796283883328615637704651 16194425824992923456556977)
                  ·
                    refine ⟨12145819368744692592417733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16194425824992923456556977 12145819368744692592417733)
                    ·
                      refine ⟨2277341131639629861078325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12145819368744692592417733 2277341131639629861078325)
                      ·
                        rfl

theorem cell23_4435106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_4435106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4435106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4435106 prefixEnd_4435106 := by exact prefixLift 4435106
  have htrace : WordTrace (prefixWord ++ tailWord_4435106) baseStart_4435106 baseEnd_4435106 := by
    simpa [prefixWord, tailWord_4435106, baseEnd_4435106] using wordTrace_append hprefix tailTrace_4435106
  have hstable : (prefixWord ++ tailWord_4435106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4435106).length < 2 ^ (prefixWord ++ tailWord_4435106).sum := by decide
  have hdescent : baseEnd_4435106 < baseStart_4435106 := by decide
  rcases family_descends (prefixWord ++ tailWord_4435106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4435109 : List Nat := [1, 3, 1, 2, 1, 5, 2, 1, 1, 3, 3]
def baseStart_4435109 : Nat := 118140960795 + 4435109 * 2 ^ 59
def prefixEnd_4435109 : Nat := 4983230072969 + 3 ^ 40 * 4435109 * 2
def baseEnd_4435109 : Nat := 2277342672081593349340811

theorem tailTrace_4435109 : CollatzResearch.WordTrace tailWord_4435109 prefixEnd_4435109 2277342672081593349340811 := by
  unfold tailWord_4435109
  simp only [CollatzResearch.WordTrace]
  refine ⟨161761714489365024158132381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107841142992910016105421587 161761714489365024158132381)
  ·
    refine ⟨60660642933511884059299643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161761714489365024158132381 60660642933511884059299643)
    ·
      refine ⟨90990964400267826088949465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60660642933511884059299643 90990964400267826088949465)
      ·
        refine ⟨68243223300200869566712099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90990964400267826088949465 68243223300200869566712099)
        ·
          refine ⟨102364834950301304350068149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68243223300200869566712099 102364834950301304350068149)
          ·
            refine ⟨9596703276590747282818889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 102364834950301304350068149 9596703276590747282818889)
            ·
              refine ⟨7197527457443060462114167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9596703276590747282818889 7197527457443060462114167)
              ·
                refine ⟨10796291186164590693171251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7197527457443060462114167 10796291186164590693171251)
                ·
                  refine ⟨16194436779246886039756877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10796291186164590693171251 16194436779246886039756877)
                  ·
                    refine ⟨6072913792217582264908829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16194436779246886039756877 6072913792217582264908829)
                    ·
                      refine ⟨2277342672081593349340811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6072913792217582264908829 2277342672081593349340811)
                      ·
                        rfl

theorem cell23_4435109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 1, 1, 3, 3].length) (baseStart_4435109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4435109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4435109 prefixEnd_4435109 := by exact prefixLift 4435109
  have htrace : WordTrace (prefixWord ++ tailWord_4435109) baseStart_4435109 baseEnd_4435109 := by
    simpa [prefixWord, tailWord_4435109, baseEnd_4435109] using wordTrace_append hprefix tailTrace_4435109
  have hstable : (prefixWord ++ tailWord_4435109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4435109).length < 2 ^ (prefixWord ++ tailWord_4435109).sum := by decide
  have hdescent : baseEnd_4435109 < baseStart_4435109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4435109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4435119 : List Nat := [1, 1, 2, 1, 2, 3, 4, 1, 3, 3, 2]
def baseStart_4435119 : Nat := 118140960795 + 4435119 * 2 ^ 59
def prefixEnd_4435119 : Nat := 4983230072969 + 3 ^ 40 * 4435119 * 2
def baseEnd_4435119 : Nat := 2277347806888138310215765

theorem tailTrace_4435119 : CollatzResearch.WordTrace tailWord_4435119 prefixEnd_4435119 2277347806888138310215765 := by
  unfold tailWord_4435119
  simp only [CollatzResearch.WordTrace]
  refine ⟨161762079219328795865996411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107841386146219197243997607 161762079219328795865996411)
  ·
    refine ⟨242643118828993193798994617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161762079219328795865996411 242643118828993193798994617)
    ·
      refine ⟨181982339121744895349245963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 242643118828993193798994617 181982339121744895349245963)
      ·
        refine ⟨272973508682617343023868945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181982339121744895349245963 272973508682617343023868945)
        ·
          refine ⟨204730131511963007267901709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 272973508682617343023868945 204730131511963007267901709)
          ·
            refine ⟨76773799316986127725463141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 204730131511963007267901709 76773799316986127725463141)
            ·
              refine ⟨14395087371934898948524339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76773799316986127725463141 14395087371934898948524339)
              ·
                refine ⟨21592631057902348422786509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14395087371934898948524339 21592631057902348422786509)
                ·
                  refine ⟨8097236646713380658544941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21592631057902348422786509 8097236646713380658544941)
                  ·
                    refine ⟨3036463742517517746954353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8097236646713380658544941 3036463742517517746954353)
                    ·
                      refine ⟨2277347806888138310215765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3036463742517517746954353 2277347806888138310215765)
                      ·
                        rfl

theorem cell23_4435119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 3, 3, 2].length) (baseStart_4435119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4435119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4435119 prefixEnd_4435119 := by exact prefixLift 4435119
  have htrace : WordTrace (prefixWord ++ tailWord_4435119) baseStart_4435119 baseEnd_4435119 := by
    simpa [prefixWord, tailWord_4435119, baseEnd_4435119] using wordTrace_append hprefix tailTrace_4435119
  have hstable : (prefixWord ++ tailWord_4435119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4435119).length < 2 ^ (prefixWord ++ tailWord_4435119).sum := by decide
  have hdescent : baseEnd_4435119 < baseStart_4435119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4435119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4435155 : List Nat := [1, 1, 1, 2, 1, 1, 1, 4, 11]
def baseStart_4435155 : Nat := 118140960795 + 4435155 * 2 ^ 59
def prefixEnd_4435155 : Nat := 4983230072969 + 3 ^ 40 * 4435155 * 2
def baseEnd_4435155 : Nat := 253040699132411129929511

theorem tailTrace_4435155 : CollatzResearch.WordTrace tailWord_4435155 prefixEnd_4435155 253040699132411129929511 := by
  unfold tailWord_4435155
  simp only [CollatzResearch.WordTrace]
  refine ⟨161763392247198374014306919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107842261498132249342871279 161763392247198374014306919)
  ·
    refine ⟨242645088370797561021460379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161763392247198374014306919 242645088370797561021460379)
    ·
      refine ⟨363967632556196341532190569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242645088370797561021460379 363967632556196341532190569)
      ·
        refine ⟨272975724417147256149142927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 363967632556196341532190569 272975724417147256149142927)
        ·
          refine ⟨409463586625720884223714391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272975724417147256149142927 409463586625720884223714391)
          ·
            refine ⟨614195379938581326335571587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 409463586625720884223714391 614195379938581326335571587)
            ·
              refine ⟨921293069907871989503357381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 614195379938581326335571587 921293069907871989503357381)
              ·
                refine ⟨172742450607725998031879509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 921293069907871989503357381 172742450607725998031879509)
                ·
                  refine ⟨253040699132411129929511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 172742450607725998031879509 253040699132411129929511)
                  ·
                    rfl

theorem cell23_4435155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 11].length) (baseStart_4435155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4435155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4435155 prefixEnd_4435155 := by exact prefixLift 4435155
  have htrace : WordTrace (prefixWord ++ tailWord_4435155) baseStart_4435155 baseEnd_4435155 := by
    simpa [prefixWord, tailWord_4435155, baseEnd_4435155] using wordTrace_append hprefix tailTrace_4435155
  have hstable : (prefixWord ++ tailWord_4435155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4435155).length < 2 ^ (prefixWord ++ tailWord_4435155).sum := by decide
  have hdescent : baseEnd_4435155 < baseStart_4435155 := by decide
  rcases family_descends (prefixWord ++ tailWord_4435155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4435172 : List Nat := [2, 3, 1, 1, 1, 2, 4, 2, 7]
def baseStart_4435172 : Nat := 118140960795 + 4435172 * 2 ^ 59
def prefixEnd_4435172 : Nat := 4983230072969 + 3 ^ 40 * 4435172 * 2
def baseEnd_4435172 : Nat := 253041669040314066983669

theorem tailTrace_4435172 : CollatzResearch.WordTrace tailWord_4435172 prefixEnd_4435172 253041669040314066983669 := by
  unfold tailWord_4435172
  simp only [CollatzResearch.WordTrace]
  refine ⟨80882006144068392958837885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107842674858757857278450513 80882006144068392958837885)
  ·
    refine ⟨30330752304025647359564207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80882006144068392958837885 30330752304025647359564207)
    ·
      refine ⟨45496128456038471039346311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30330752304025647359564207 45496128456038471039346311)
      ·
        refine ⟨68244192684057706559019467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45496128456038471039346311 68244192684057706559019467)
        ·
          refine ⟨102366289026086559838529201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68244192684057706559019467 102366289026086559838529201)
          ·
            refine ⟨76774716769564919878896901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102366289026086559838529201 76774716769564919878896901)
            ·
              refine ⟨14395259394293422477293169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76774716769564919878896901 14395259394293422477293169)
              ·
                refine ⟨10796444545720066857969877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14395259394293422477293169 10796444545720066857969877)
                ·
                  refine ⟨253041669040314066983669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10796444545720066857969877 253041669040314066983669)
                  ·
                    rfl

theorem cell23_4435172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 2, 7].length) (baseStart_4435172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4435172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4435172 prefixEnd_4435172 := by exact prefixLift 4435172
  have htrace : WordTrace (prefixWord ++ tailWord_4435172) baseStart_4435172 baseEnd_4435172 := by
    simpa [prefixWord, tailWord_4435172, baseEnd_4435172] using wordTrace_append hprefix tailTrace_4435172
  have hstable : (prefixWord ++ tailWord_4435172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4435172).length < 2 ^ (prefixWord ++ tailWord_4435172).sum := by decide
  have hdescent : baseEnd_4435172 < baseStart_4435172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4435172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4435209 : List Nat := [1, 2, 1, 1, 3, 3, 2, 1, 2, 5, 2]
def baseStart_4435209 : Nat := 118140960795 + 4435209 * 2 ^ 59
def prefixEnd_4435209 : Nat := 4983230072969 + 3 ^ 40 * 4435209 * 2
def baseEnd_4435209 : Nat := 2277394020147042958090351

theorem tailTrace_4435209 : CollatzResearch.WordTrace tailWord_4435209 prefixEnd_4435209 2277394020147042958090351 := by
  unfold tailWord_4435209
  simp only [CollatzResearch.WordTrace]
  refine ⟨161765361789002741236772681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107843574526001827491181787 161765361789002741236772681)
  ·
    refine ⟨121324021341752055927579511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161765361789002741236772681 121324021341752055927579511)
    ·
      refine ⟨181986032012628083891369267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121324021341752055927579511 181986032012628083891369267)
      ·
        refine ⟨272979048018942125837053901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181986032012628083891369267 272979048018942125837053901)
        ·
          refine ⟨102367143007103297188895213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 272979048018942125837053901 102367143007103297188895213)
          ·
            refine ⟨38387678627663736445835705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102367143007103297188895213 38387678627663736445835705)
            ·
              refine ⟨28790758970747802334376779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38387678627663736445835705 28790758970747802334376779)
              ·
                refine ⟨43186138456121703501565169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28790758970747802334376779 43186138456121703501565169)
                ·
                  refine ⟨32389603842091277626173877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43186138456121703501565169 32389603842091277626173877)
                  ·
                    refine ⟨3036525360196057277453801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32389603842091277626173877 3036525360196057277453801)
                    ·
                      refine ⟨2277394020147042958090351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3036525360196057277453801 2277394020147042958090351)
                      ·
                        rfl

theorem cell23_4435209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 5, 2].length) (baseStart_4435209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4435209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4435209 prefixEnd_4435209 := by exact prefixLift 4435209
  have htrace : WordTrace (prefixWord ++ tailWord_4435209) baseStart_4435209 baseEnd_4435209 := by
    simpa [prefixWord, tailWord_4435209, baseEnd_4435209] using wordTrace_append hprefix tailTrace_4435209
  have hstable : (prefixWord ++ tailWord_4435209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4435209).length < 2 ^ (prefixWord ++ tailWord_4435209).sum := by decide
  have hdescent : baseEnd_4435209 < baseStart_4435209 := by decide
  rcases family_descends (prefixWord ++ tailWord_4435209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4435212 : List Nat := [2, 2, 1, 2, 2, 3, 1, 1, 1, 1, 7]
def baseStart_4435212 : Nat := 118140960795 + 4435212 * 2 ^ 59
def prefixEnd_4435212 : Nat := 4983230072969 + 3 ^ 40 * 4435212 * 2
def baseEnd_4435212 : Nat := 2277395560589006446352837

theorem tailTrace_4435212 : CollatzResearch.WordTrace tailWord_4435212 prefixEnd_4435212 2277395560589006446352837 := by
  unfold tailWord_4435212
  simp only [CollatzResearch.WordTrace]
  refine ⟨80882735603995936374565945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107843647471994581832754593 80882735603995936374565945)
  ·
    refine ⟨60662051702996952280924459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80882735603995936374565945 60662051702996952280924459)
    ·
      refine ⟨90993077554495428421386689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60662051702996952280924459 90993077554495428421386689)
      ·
        refine ⟨68244808165871571316040017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90993077554495428421386689 68244808165871571316040017)
        ·
          refine ⟨51183606124403678487030013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68244808165871571316040017 51183606124403678487030013)
          ·
            refine ⟨19193852296651379432636255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51183606124403678487030013 19193852296651379432636255)
            ·
              refine ⟨28790778444977069148954383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19193852296651379432636255 28790778444977069148954383)
              ·
                refine ⟨43186167667465603723431575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28790778444977069148954383 43186167667465603723431575)
                ·
                  refine ⟨64779251501198405585147363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43186167667465603723431575 64779251501198405585147363)
                  ·
                    refine ⟨97168877251797608377721045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 64779251501198405585147363 97168877251797608377721045)
                    ·
                      refine ⟨2277395560589006446352837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 97168877251797608377721045 2277395560589006446352837)
                      ·
                        rfl

theorem cell23_4435212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_4435212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4435212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4435212 prefixEnd_4435212 := by exact prefixLift 4435212
  have htrace : WordTrace (prefixWord ++ tailWord_4435212) baseStart_4435212 baseEnd_4435212 := by
    simpa [prefixWord, tailWord_4435212, baseEnd_4435212] using wordTrace_append hprefix tailTrace_4435212
  have hstable : (prefixWord ++ tailWord_4435212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4435212).length < 2 ^ (prefixWord ++ tailWord_4435212).sum := by decide
  have hdescent : baseEnd_4435212 < baseStart_4435212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4435212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4435323 : List Nat := [1, 1, 1, 1, 1, 6, 1, 6, 1, 1, 3]
def baseStart_4435323 : Nat := 118140960795 + 4435323 * 2 ^ 59
def prefixEnd_4435323 : Nat := 4983230072969 + 3 ^ 40 * 4435323 * 2
def baseEnd_4435323 : Nat := 2277452556941655512064827

theorem tailTrace_4435323 : CollatzResearch.WordTrace tailWord_4435323 prefixEnd_4435323 2277452556941655512064827 := by
  unfold tailWord_4435323
  simp only [CollatzResearch.WordTrace]
  refine ⟨161769519710589738706422623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107846346473726492470948415 161769519710589738706422623)
  ·
    refine ⟨242654279565884608059633935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161769519710589738706422623 242654279565884608059633935)
    ·
      refine ⟨363981419348826912089450903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242654279565884608059633935 363981419348826912089450903)
      ·
        refine ⟨545972129023240368134176355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 363981419348826912089450903 545972129023240368134176355)
        ·
          refine ⟨818958193534860552201264533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 545972129023240368134176355 818958193534860552201264533)
          ·
            refine ⟨38388665321946588384434275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 818958193534860552201264533 38388665321946588384434275)
            ·
              refine ⟨57582997982919882576651413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38388665321946588384434275 57582997982919882576651413)
              ·
                refine ⟨2699203030449369495780535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 57582997982919882576651413 2699203030449369495780535)
                ·
                  refine ⟨4048804545674054243670803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2699203030449369495780535 4048804545674054243670803)
                  ·
                    refine ⟨6073206818511081365506205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4048804545674054243670803 6073206818511081365506205)
                    ·
                      refine ⟨2277452556941655512064827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6073206818511081365506205 2277452556941655512064827)
                      ·
                        rfl

theorem cell23_4435323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 6, 1, 1, 3].length) (baseStart_4435323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4435323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4435323 prefixEnd_4435323 := by exact prefixLift 4435323
  have htrace : WordTrace (prefixWord ++ tailWord_4435323) baseStart_4435323 baseEnd_4435323 := by
    simpa [prefixWord, tailWord_4435323, baseEnd_4435323] using wordTrace_append hprefix tailTrace_4435323
  have hstable : (prefixWord ++ tailWord_4435323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4435323).length < 2 ^ (prefixWord ++ tailWord_4435323).sum := by decide
  have hdescent : baseEnd_4435323 < baseStart_4435323 := by decide
  rcases family_descends (prefixWord ++ tailWord_4435323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4435330 : List Nat := [3, 4, 2, 1, 1, 2, 3, 1, 6]
def baseStart_4435330 : Nat := 118140960795 + 4435330 * 2 ^ 59
def prefixEnd_4435330 : Nat := 4983230072969 + 3 ^ 40 * 4435330 * 2
def baseEnd_4435330 : Nat := 253050683478470776075255

theorem tailTrace_4435330 : CollatzResearch.WordTrace tailWord_4435330 prefixEnd_4435330 253050683478470776075255 := by
  unfold tailWord_4435330
  simp only [CollatzResearch.WordTrace]
  refine ⟨40442443755391094725481861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107846516681042919267951629 40442443755391094725481861)
  ·
    refine ⟨7582958204135830261027849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40442443755391094725481861 7582958204135830261027849)
    ·
      refine ⟨5687218653101872695770887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7582958204135830261027849 5687218653101872695770887)
      ·
        refine ⟨8530827979652809043656331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5687218653101872695770887 8530827979652809043656331)
        ·
          refine ⟨12796241969479213565484497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8530827979652809043656331 12796241969479213565484497)
          ·
            refine ⟨9597181477109410174113373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12796241969479213565484497 9597181477109410174113373)
            ·
              refine ⟨3598943053916028815292515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9597181477109410174113373 3598943053916028815292515)
              ·
                refine ⟨5398414580874043222938773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3598943053916028815292515 5398414580874043222938773)
                ·
                  refine ⟨253050683478470776075255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5398414580874043222938773 253050683478470776075255)
                  ·
                    rfl

theorem cell23_4435330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_4435330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4435330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4435330 prefixEnd_4435330 := by exact prefixLift 4435330
  have htrace : WordTrace (prefixWord ++ tailWord_4435330) baseStart_4435330 baseEnd_4435330 := by
    simpa [prefixWord, tailWord_4435330, baseEnd_4435330] using wordTrace_append hprefix tailTrace_4435330
  have hstable : (prefixWord ++ tailWord_4435330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4435330).length < 2 ^ (prefixWord ++ tailWord_4435330).sum := by decide
  have hdescent : baseEnd_4435330 < baseStart_4435330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4435330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4435357 : List Nat := [1, 4, 2, 1, 3, 3, 1, 3, 1, 1, 3]
def baseStart_4435357 : Nat := 118140960795 + 4435357 * 2 ^ 59
def prefixEnd_4435357 : Nat := 4983230072969 + 3 ^ 40 * 4435357 * 2
def baseEnd_4435357 : Nat := 2277470015283908379039671

theorem tailTrace_4435357 : CollatzResearch.WordTrace tailWord_4435357 prefixEnd_4435357 2277470015283908379039671 := by
  unfold tailWord_4435357
  simp only [CollatzResearch.WordTrace]
  refine ⟨161770759792466562513160325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107847173194977708342106883 161770759792466562513160325)
  ·
    refine ⟨30332017461087480471217561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 161770759792466562513160325 30332017461087480471217561)
    ·
      refine ⟨22749013095815610353413171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30332017461087480471217561 22749013095815610353413171)
      ·
        refine ⟨34123519643723415530119757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22749013095815610353413171 34123519643723415530119757)
        ·
          refine ⟨12796319866396280823794909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34123519643723415530119757 12796319866396280823794909)
          ·
            refine ⟨4798619949898605308923091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12796319866396280823794909 4798619949898605308923091)
            ·
              refine ⟨7197929924847907963384637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4798619949898605308923091 7197929924847907963384637)
              ·
                refine ⟨2699223721817965486269239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7197929924847907963384637 2699223721817965486269239)
                ·
                  refine ⟨4048835582726948229403859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2699223721817965486269239 4048835582726948229403859)
                  ·
                    refine ⟨6073253374090422344105789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4048835582726948229403859 6073253374090422344105789)
                    ·
                      refine ⟨2277470015283908379039671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6073253374090422344105789 2277470015283908379039671)
                      ·
                        rfl

theorem cell23_4435357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 3, 1, 1, 3].length) (baseStart_4435357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4435357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4435357 prefixEnd_4435357 := by exact prefixLift 4435357
  have htrace : WordTrace (prefixWord ++ tailWord_4435357) baseStart_4435357 baseEnd_4435357 := by
    simpa [prefixWord, tailWord_4435357, baseEnd_4435357] using wordTrace_append hprefix tailTrace_4435357
  have hstable : (prefixWord ++ tailWord_4435357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4435357).length < 2 ^ (prefixWord ++ tailWord_4435357).sum := by decide
  have hdescent : baseEnd_4435357 < baseStart_4435357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4435357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4435373 : List Nat := [1, 5, 2, 2, 1, 1, 2, 1, 4, 4]
def baseStart_4435373 : Nat := 118140960795 + 4435373 * 2 ^ 59
def prefixEnd_4435373 : Nat := 4983230072969 + 3 ^ 40 * 4435373 * 2
def baseEnd_4435373 : Nat := 759159410324793438813199

theorem tailTrace_4435373 : CollatzResearch.WordTrace tailWord_4435373 prefixEnd_4435373 759159410324793438813199 := by
  unfold tailWord_4435373
  simp only [CollatzResearch.WordTrace]
  refine ⟨161771343360408597245742773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107847562240272398163828515 161771343360408597245742773)
  ·
    refine ⟨15166063440038305991788385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 161771343360408597245742773 15166063440038305991788385)
    ·
      refine ⟨11374547580028729493841289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15166063440038305991788385 11374547580028729493841289)
      ·
        refine ⟨8530910685021547120380967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11374547580028729493841289 8530910685021547120380967)
        ·
          refine ⟨12796366027532320680571451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8530910685021547120380967 12796366027532320680571451)
          ·
            refine ⟨19194549041298481020857177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12796366027532320680571451 19194549041298481020857177)
            ·
              refine ⟨14395911780973860765642883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19194549041298481020857177 14395911780973860765642883)
              ·
                refine ⟨21593867671460791148464325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14395911780973860765642883 21593867671460791148464325)
                ·
                  refine ⟨4048850188398898340337061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21593867671460791148464325 4048850188398898340337061)
                  ·
                    refine ⟨759159410324793438813199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4048850188398898340337061 759159410324793438813199)
                    ·
                      rfl

theorem cell23_4435373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_4435373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4435373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4435373 prefixEnd_4435373 := by exact prefixLift 4435373
  have htrace : WordTrace (prefixWord ++ tailWord_4435373) baseStart_4435373 baseEnd_4435373 := by
    simpa [prefixWord, tailWord_4435373, baseEnd_4435373] using wordTrace_append hprefix tailTrace_4435373
  have hstable : (prefixWord ++ tailWord_4435373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4435373).length < 2 ^ (prefixWord ++ tailWord_4435373).sum := by decide
  have hdescent : baseEnd_4435373 < baseStart_4435373 := by decide
  rcases family_descends (prefixWord ++ tailWord_4435373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4435389 : List Nat := [1, 4, 1, 2, 2, 1, 1, 1, 2, 2, 6]
def baseStart_4435389 : Nat := 118140960795 + 4435389 * 2 ^ 59
def prefixEnd_4435389 : Nat := 4983230072969 + 3 ^ 40 * 4435389 * 2
def baseEnd_4435389 : Nat := 2277486446664852253839523

theorem tailTrace_4435389 : CollatzResearch.WordTrace tailWord_4435389 prefixEnd_4435389 2277486446664852253839523 := by
  unfold tailWord_4435389
  simp only [CollatzResearch.WordTrace]
  refine ⟨161771926928350631978325221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107847951285567087985550147 161771926928350631978325221)
  ·
    refine ⟨30332236299065743495935979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 161771926928350631978325221 30332236299065743495935979)
    ·
      refine ⟨45498354448598615243903969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30332236299065743495935979 45498354448598615243903969)
      ·
        refine ⟨34123765836448961432927977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45498354448598615243903969 34123765836448961432927977)
        ·
          refine ⟨25592824377336721074695983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34123765836448961432927977 25592824377336721074695983)
          ·
            refine ⟨38389236566005081612043975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25592824377336721074695983 38389236566005081612043975)
            ·
              refine ⟨57583854849007622418065963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38389236566005081612043975 57583854849007622418065963)
              ·
                refine ⟨86375782273511433627098945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57583854849007622418065963 86375782273511433627098945)
                ·
                  refine ⟨64781836705133575220324209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86375782273511433627098945 64781836705133575220324209)
                  ·
                    refine ⟨48586377528850181415243157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 64781836705133575220324209 48586377528850181415243157)
                    ·
                      refine ⟨2277486446664852253839523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48586377528850181415243157 2277486446664852253839523)
                      ·
                        rfl

theorem cell23_4435389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_4435389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4435389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4435389 prefixEnd_4435389 := by exact prefixLift 4435389
  have htrace : WordTrace (prefixWord ++ tailWord_4435389) baseStart_4435389 baseEnd_4435389 := by
    simpa [prefixWord, tailWord_4435389, baseEnd_4435389] using wordTrace_append hprefix tailTrace_4435389
  have hstable : (prefixWord ++ tailWord_4435389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4435389).length < 2 ^ (prefixWord ++ tailWord_4435389).sum := by decide
  have hdescent : baseEnd_4435389 < baseStart_4435389 := by decide
  rcases family_descends (prefixWord ++ tailWord_4435389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4435439 : List Nat := [1, 1, 2, 1, 4, 1, 2, 2, 1, 3, 5]
def baseStart_4435439 : Nat := 118140960795 + 4435439 * 2 ^ 59
def prefixEnd_4435439 : Nat := 4983230072969 + 3 ^ 40 * 4435439 * 2
def baseEnd_4435439 : Nat := 2277512120697577058214293

theorem tailTrace_4435439 : CollatzResearch.WordTrace tailWord_4435439 prefixEnd_4435439 2277512120697577058214293 := by
  unfold tailWord_4435439
  simp only [CollatzResearch.WordTrace]
  refine ⟨161773750578169490517645371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107849167052112993678430247 161773750578169490517645371)
  ·
    refine ⟨242660625867254235776468057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161773750578169490517645371 242660625867254235776468057)
    ·
      refine ⟨181995469400440676832351043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 242660625867254235776468057 181995469400440676832351043)
      ·
        refine ⟨272993204100661015248526565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181995469400440676832351043 272993204100661015248526565)
        ·
          refine ⟨51186225768873940359098731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 272993204100661015248526565 51186225768873940359098731)
          ·
            refine ⟨76779338653310910538648097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51186225768873940359098731 76779338653310910538648097)
            ·
              refine ⟨57584503989983182903986073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76779338653310910538648097 57584503989983182903986073)
              ·
                refine ⟨43188377992487387177989555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57584503989983182903986073 43188377992487387177989555)
                ·
                  refine ⟨64782566988731080766984333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43188377992487387177989555 64782566988731080766984333)
                  ·
                    refine ⟨24293462620774155287619125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 64782566988731080766984333 24293462620774155287619125)
                    ·
                      refine ⟨2277512120697577058214293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24293462620774155287619125 2277512120697577058214293)
                      ·
                        rfl

theorem cell23_4435439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 3, 5].length) (baseStart_4435439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4435439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4435439 prefixEnd_4435439 := by exact prefixLift 4435439
  have htrace : WordTrace (prefixWord ++ tailWord_4435439) baseStart_4435439 baseEnd_4435439 := by
    simpa [prefixWord, tailWord_4435439, baseEnd_4435439] using wordTrace_append hprefix tailTrace_4435439
  have hstable : (prefixWord ++ tailWord_4435439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4435439).length < 2 ^ (prefixWord ++ tailWord_4435439).sum := by decide
  have hdescent : baseEnd_4435439 < baseStart_4435439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4435439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4435446 : List Nat := [5, 1, 1, 1, 2, 2, 1, 1, 1, 8]
def baseStart_4435446 : Nat := 118140960795 + 4435446 * 2 ^ 59
def prefixEnd_4435446 : Nat := 4983230072969 + 3 ^ 40 * 4435446 * 2
def baseEnd_4435446 : Nat := 759171905020719510275587

theorem tailTrace_4435446 : CollatzResearch.WordTrace tailWord_4435446 prefixEnd_4435446 759171905020719510275587 := by
  unfold tailWord_4435446
  simp only [CollatzResearch.WordTrace]
  refine ⟨10110875368071508169571887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 107849337259429420475433461 10110875368071508169571887)
  ·
    refine ⟨15166313052107262254357831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10110875368071508169571887 15166313052107262254357831)
    ·
      refine ⟨22749469578160893381536747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15166313052107262254357831 22749469578160893381536747)
      ·
        refine ⟨34124204367241340072305121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22749469578160893381536747 34124204367241340072305121)
        ·
          refine ⟨25593153275431005054228841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34124204367241340072305121 25593153275431005054228841)
          ·
            refine ⟨19194864956573253790671631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25593153275431005054228841 19194864956573253790671631)
            ·
              refine ⟨28792297434859880686007447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19194864956573253790671631 28792297434859880686007447)
              ·
                refine ⟨43188446152289821029011171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28792297434859880686007447 43188446152289821029011171)
                ·
                  refine ⟨64782669228434731543516757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43188446152289821029011171 64782669228434731543516757)
                  ·
                    refine ⟨759171905020719510275587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 64782669228434731543516757 759171905020719510275587)
                    ·
                      rfl

theorem cell23_4435446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_4435446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4435446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4435446 prefixEnd_4435446 := by exact prefixLift 4435446
  have htrace : WordTrace (prefixWord ++ tailWord_4435446) baseStart_4435446 baseEnd_4435446 := by
    simpa [prefixWord, tailWord_4435446, baseEnd_4435446] using wordTrace_append hprefix tailTrace_4435446
  have hstable : (prefixWord ++ tailWord_4435446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4435446).length < 2 ^ (prefixWord ++ tailWord_4435446).sum := by decide
  have hdescent : baseEnd_4435446 < baseStart_4435446 := by decide
  rcases family_descends (prefixWord ++ tailWord_4435446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4435453 : List Nat := [1, 4, 1, 1, 1, 4, 1, 3, 1, 4, 2]
def baseStart_4435453 : Nat := 118140960795 + 4435453 * 2 ^ 59
def prefixEnd_4435453 : Nat := 4983230072969 + 3 ^ 40 * 4435453 * 2
def baseEnd_4435453 : Nat := 2277519309426740003439229

theorem tailTrace_4435453 : CollatzResearch.WordTrace tailWord_4435453 prefixEnd_4435453 2277519309426740003439229 := by
  unfold tailWord_4435453
  simp only [CollatzResearch.WordTrace]
  refine ⟨161774261200118770908655013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107849507466745847272436675 161774261200118770908655013)
  ·
    refine ⟨30332673975022269545372815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 161774261200118770908655013 30332673975022269545372815)
    ·
      refine ⟨45499010962533404318059223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30332673975022269545372815 45499010962533404318059223)
      ·
        refine ⟨68248516443800106477088835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45499010962533404318059223 68248516443800106477088835)
        ·
          refine ⟨102372774665700159715633253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68248516443800106477088835 102372774665700159715633253)
          ·
            refine ⟨19194895249818779946681235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 102372774665700159715633253 19194895249818779946681235)
            ·
              refine ⟨28792342874728169920021853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19194895249818779946681235 28792342874728169920021853)
              ·
                refine ⟨10797128578023063720008195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28792342874728169920021853 10797128578023063720008195)
                ·
                  refine ⟨16195692867034595580012293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10797128578023063720008195 16195692867034595580012293)
                  ·
                    refine ⟨3036692412568986671252305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16195692867034595580012293 3036692412568986671252305)
                    ·
                      refine ⟨2277519309426740003439229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3036692412568986671252305 2277519309426740003439229)
                      ·
                        rfl

theorem cell23_4435453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 3, 1, 4, 2].length) (baseStart_4435453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4435453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4435453 prefixEnd_4435453 := by exact prefixLift 4435453
  have htrace : WordTrace (prefixWord ++ tailWord_4435453) baseStart_4435453 baseEnd_4435453 := by
    simpa [prefixWord, tailWord_4435453, baseEnd_4435453] using wordTrace_append hprefix tailTrace_4435453
  have hstable : (prefixWord ++ tailWord_4435453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4435453).length < 2 ^ (prefixWord ++ tailWord_4435453).sum := by decide
  have hdescent : baseEnd_4435453 < baseStart_4435453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4435453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4435527 : List Nat := [1, 1, 4, 1, 6, 1, 1, 3, 5]
def baseStart_4435527 : Nat := 118140960795 + 4435527 * 2 ^ 59
def prefixEnd_4435527 : Nat := 4983230072969 + 3 ^ 40 * 4435527 * 2
def baseEnd_4435527 : Nat := 253061922999463634879321

theorem tailTrace_4435527 : CollatzResearch.WordTrace tailWord_4435527 prefixEnd_4435527 253061922999463634879321 := by
  unfold tailWord_4435527
  simp only [CollatzResearch.WordTrace]
  refine ⟨161776960201850681546848835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107851306801233787697899223 161776960201850681546848835)
  ·
    refine ⟨242665440302776022320273253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161776960201850681546848835 242665440302776022320273253)
    ·
      refine ⟨45499770056770504185051235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 242665440302776022320273253 45499770056770504185051235)
      ·
        refine ⟨68249655085155756277576853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45499770056770504185051235 68249655085155756277576853)
        ·
          refine ⟨3199202582116676075511415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 68249655085155756277576853 3199202582116676075511415)
          ·
            refine ⟨4798803873175014113267123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3199202582116676075511415 4798803873175014113267123)
            ·
              refine ⟨7198205809762521169900685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4798803873175014113267123 7198205809762521169900685)
              ·
                refine ⟨2699327178660945438712757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7198205809762521169900685 2699327178660945438712757)
                ·
                  refine ⟨253061922999463634879321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2699327178660945438712757 253061922999463634879321)
                  ·
                    rfl

theorem cell23_4435527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 3, 5].length) (baseStart_4435527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4435527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4435527 prefixEnd_4435527 := by exact prefixLift 4435527
  have htrace : WordTrace (prefixWord ++ tailWord_4435527) baseStart_4435527 baseEnd_4435527 := by
    simpa [prefixWord, tailWord_4435527, baseEnd_4435527] using wordTrace_append hprefix tailTrace_4435527
  have hstable : (prefixWord ++ tailWord_4435527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4435527).length < 2 ^ (prefixWord ++ tailWord_4435527).sum := by decide
  have hdescent : baseEnd_4435527 < baseStart_4435527 := by decide
  rcases family_descends (prefixWord ++ tailWord_4435527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4435543 : List Nat := [1, 1, 3, 2, 2, 4, 1, 2, 2, 1, 4]
def baseStart_4435543 : Nat := 118140960795 + 4435543 * 2 ^ 59
def prefixEnd_4435543 : Nat := 4983230072969 + 3 ^ 40 * 4435543 * 2
def baseEnd_4435543 : Nat := 2277565522685644651313815

theorem tailTrace_4435543 : CollatzResearch.WordTrace tailWord_4435543 prefixEnd_4435543 2277565522685644651313815 := by
  unfold tailWord_4435543
  simp only [CollatzResearch.WordTrace]
  refine ⟨161777543769792716279431283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107851695846528477519620855 161777543769792716279431283)
  ·
    refine ⟨242666315654689074419146925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161777543769792716279431283 242666315654689074419146925)
    ·
      refine ⟨90999868370508402907180097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 242666315654689074419146925 90999868370508402907180097)
      ·
        refine ⟨68249901277881302180385073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90999868370508402907180097 68249901277881302180385073)
        ·
          refine ⟨51187425958410976635288805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68249901277881302180385073 51187425958410976635288805)
          ·
            refine ⟨9597642367202058119116651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51187425958410976635288805 9597642367202058119116651)
            ·
              refine ⟨14396463550803087178674977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9597642367202058119116651 14396463550803087178674977)
              ·
                refine ⟨10797347663102315384006233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14396463550803087178674977 10797347663102315384006233)
                ·
                  refine ⟨8098010747326736538004675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10797347663102315384006233 8098010747326736538004675)
                  ·
                    refine ⟨12147016120990104807007013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8098010747326736538004675 12147016120990104807007013)
                    ·
                      refine ⟨2277565522685644651313815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12147016120990104807007013 2277565522685644651313815)
                      ·
                        rfl

theorem cell23_4435543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 2, 2, 1, 4].length) (baseStart_4435543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4435543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4435543 prefixEnd_4435543 := by exact prefixLift 4435543
  have htrace : WordTrace (prefixWord ++ tailWord_4435543) baseStart_4435543 baseEnd_4435543 := by
    simpa [prefixWord, tailWord_4435543, baseEnd_4435543] using wordTrace_append hprefix tailTrace_4435543
  have hstable : (prefixWord ++ tailWord_4435543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4435543).length < 2 ^ (prefixWord ++ tailWord_4435543).sum := by decide
  have hdescent : baseEnd_4435543 < baseStart_4435543 := by decide
  rcases family_descends (prefixWord ++ tailWord_4435543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4435604 : List Nat := [2, 4, 2, 2, 2, 1, 1, 4, 1, 4]
def baseStart_4435604 : Nat := 118140960795 + 4435604 * 2 ^ 59
def prefixEnd_4435604 : Nat := 4983230072969 + 3 ^ 40 * 4435604 * 2
def baseEnd_4435604 : Nat := 759198948335189637550345

theorem tailTrace_4435604 : CollatzResearch.WordTrace tailWord_4435604 prefixEnd_4435604 759198948335189637550345 := by
  unfold tailWord_4435604
  simp only [CollatzResearch.WordTrace]
  refine ⟨80889884311285861848700933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107853179081714482464934577 80889884311285861848700933)
  ·
    refine ⟨15166853308366099096631425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80889884311285861848700933 15166853308366099096631425)
    ·
      refine ⟨11375139981274574322473569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15166853308366099096631425 11375139981274574322473569)
      ·
        refine ⟨8531354985955930741855177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11375139981274574322473569 8531354985955930741855177)
        ·
          refine ⟨6398516239466948056391383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8531354985955930741855177 6398516239466948056391383)
          ·
            refine ⟨9597774359200422084587075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6398516239466948056391383 9597774359200422084587075)
            ·
              refine ⟨14396661538800633126880613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9597774359200422084587075 14396661538800633126880613)
              ·
                refine ⟨2699374038525118711290115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14396661538800633126880613 2699374038525118711290115)
                ·
                  refine ⟨4049061057787678066935173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2699374038525118711290115 4049061057787678066935173)
                  ·
                    refine ⟨759198948335189637550345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4049061057787678066935173 759198948335189637550345)
                    ·
                      rfl

theorem cell23_4435604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_4435604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4435604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4435604 prefixEnd_4435604 := by exact prefixLift 4435604
  have htrace : WordTrace (prefixWord ++ tailWord_4435604) baseStart_4435604 baseEnd_4435604 := by
    simpa [prefixWord, tailWord_4435604, baseEnd_4435604] using wordTrace_append hprefix tailTrace_4435604
  have hstable : (prefixWord ++ tailWord_4435604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4435604).length < 2 ^ (prefixWord ++ tailWord_4435604).sum := by decide
  have hdescent : baseEnd_4435604 < baseStart_4435604 := by decide
  rcases family_descends (prefixWord ++ tailWord_4435604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4435637 : List Nat := [1, 3, 3, 3, 2, 1, 1, 1, 1, 5, 2]
def baseStart_4435637 : Nat := 118140960795 + 4435637 * 2 ^ 59
def prefixEnd_4435637 : Nat := 4983230072969 + 3 ^ 40 * 4435637 * 2
def baseEnd_4435637 : Nat := 2277613789867167283538383

theorem tailTrace_4435637 : CollatzResearch.WordTrace tailWord_4435637 prefixEnd_4435637 2277613789867167283538383 := by
  unfold tailWord_4435637
  simp only [CollatzResearch.WordTrace]
  refine ⟨161780972231452170333353165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107853981487634780222235443 161780972231452170333353165)
  ·
    refine ⟨60667864586794563875007437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161780972231452170333353165 60667864586794563875007437)
    ·
      refine ⟨22750449220047961453127789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60667864586794563875007437 22750449220047961453127789)
      ·
        refine ⟨8531418457517985544922921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22750449220047961453127789 8531418457517985544922921)
        ·
          refine ⟨6398563843138489158692191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8531418457517985544922921 6398563843138489158692191)
          ·
            refine ⟨9597845764707733738038287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6398563843138489158692191 9597845764707733738038287)
            ·
              refine ⟨14396768647061600607057431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9597845764707733738038287 14396768647061600607057431)
              ·
                refine ⟨21595152970592400910586147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14396768647061600607057431 21595152970592400910586147)
                ·
                  refine ⟨32392729455888601365879221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21595152970592400910586147 32392729455888601365879221)
                  ·
                    refine ⟨3036818386489556378051177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32392729455888601365879221 3036818386489556378051177)
                    ·
                      refine ⟨2277613789867167283538383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3036818386489556378051177 2277613789867167283538383)
                      ·
                        rfl

theorem cell23_4435637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_4435637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4435637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4435637 prefixEnd_4435637 := by exact prefixLift 4435637
  have htrace : WordTrace (prefixWord ++ tailWord_4435637) baseStart_4435637 baseEnd_4435637 := by
    simpa [prefixWord, tailWord_4435637, baseEnd_4435637] using wordTrace_append hprefix tailTrace_4435637
  have hstable : (prefixWord ++ tailWord_4435637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4435637).length < 2 ^ (prefixWord ++ tailWord_4435637).sum := by decide
  have hdescent : baseEnd_4435637 < baseStart_4435637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4435637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
